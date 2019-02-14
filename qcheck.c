/*
 * Copyright 2005-2018 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 *
 * Copyright 2005-2010 Ned Ludd        - <solar@gentoo.org>
 * Copyright 2005-2014 Mike Frysinger  - <vapier@gentoo.org>
 */

#include "sys/xattr.h"
#include "math.h"

#ifdef APPLET_qcheck

#define QCHECK_FLAGS "s:uABHTmdxcPp" COMMON_FLAGS
static struct option const qcheck_long_opts[] = {
	{"skip",            a_argument, NULL, 's'},
	{"update",         no_argument, NULL, 'u'},
	{"noafk",          no_argument, NULL, 'A'},
	{"badonly",        no_argument, NULL, 'B'},
	{"nohash",         no_argument, NULL, 'H'},
	{"nomtime",        no_argument, NULL, 'T'},
	{"nomode",         no_argument, NULL, 'm'},
	{"nosha",          no_argument, NULL, 'd'},
	{"nopax",          no_argument, NULL, 'x'},
	{"nocaps",         no_argument, NULL, 'c'},
	{"skip-protected", no_argument, NULL, 'P'},
	{"prelink",        no_argument, NULL, 'p'},
	COMMON_LONG_OPTS
};
static const char * const qcheck_opts_help[] = {
	"Ignore files matching the regular expression <arg>",
	"Update missing files, chksum and mtimes for packages",
	"Ignore missing files",
	"Only print pkgs containing bad files",
	"Ignore differing/unknown file chksums",
	"Ignore differing file mtimes",
	"Ignore differing file modes",
	"Ignore differing file SHA digests",
	"Ignore differing file attributes for pax markings",
	"Ignore differing file attributes for POSIX capability",
	"Ignore files in CONFIG_PROTECT-ed paths",
	"Undo prelink when calculating checksums",
	COMMON_OPTS_HELP
};
#define qcheck_usage(ret) usage(ret, QCHECK_FLAGS, qcheck_long_opts, qcheck_opts_help, NULL, lookup_applet_idx("qcheck"))

#define qcprintf(fmt, args...) do { if (!state->bad_only) printf(_(fmt), ## args); } while (0)

#define SHA1_DIGEST_LENGTH 40
#define SHA256_DIGEST_LENGTH 64
#define SHA512_DIGEST_LENGTH 128

struct qcheck_opt_state {
	array_t *atoms;
	array_t *regex_arr;
	bool bad_only;
	bool qc_update;
	bool chk_afk;
	bool chk_hash;
	bool chk_mtime;
	bool chk_mode;
	bool chk_sha_digests;
	bool chk_attrs_pax;
	bool chk_attrs_caps;
	bool chk_config_protect;
	bool undo_prelink;
};

/* Move to the right pos in fp_contents_caps, read chars, put into fentry_caps and return */
static int get_recorded_meta(char *fentry_caps, FILE *fp_contents_caps, int entry_id, int record_len)
{
	int ret = 0;
	int linelen = record_len + 1; /* including newline */
	int bytes = linelen * (entry_id-1);
	fseek(fp_contents_caps, bytes, SEEK_SET);

	if (fgets(fentry_caps, linelen, fp_contents_caps) == NULL)
		ret = 1;

	return ret;
}

/* Get DIGEST from recorded CONTENTS_DIGESTS_* */
static int cmp_recorded_digest(FILE * fp, int entry_id, char * fname, const char * hash_algo)
{
	int ret = 1;
	int record_len = 0;

	if (strcmp(hash_algo,"SHA1") == 0)
		record_len = SHA1_DIGEST_LENGTH;
	if (strcmp(hash_algo,"SHA256") == 0)
		record_len = SHA256_DIGEST_LENGTH;
	if (strcmp(hash_algo,"SHA512") == 0)
		record_len = SHA512_DIGEST_LENGTH;

	char * fentry_dig = xcalloc(record_len+1, sizeof(char));
	char * file_digest = xcalloc(record_len+1, sizeof(char));

	/* Get DIGEST from recorded CONTENTS_DIGESTS_* */
	if (get_recorded_meta(fentry_dig, fp, entry_id, record_len) == 1) {
		qcprintf("Error in CONTENTS_DIGESTS_%s, couldn't find entry: %s\n", hash_algo, fname);

		free(fentry_dig);
		free(file_digest);

		return 1;
	}

	/* Get DIGEST from file using shasum */
	external_check_sha(file_digest, fname, (char *)hash_algo);

	/* See if digests match */
	if (strcmp(fentry_dig, file_digest) != 0) {
		qcprintf(" %s%s-DIGEST%s: %s", RED, hash_algo, NORM, fname);
		if (verbose)
			qcprintf(" ('%s' should be '%s')", file_digest, fentry_dig);
		qcprintf("\n");
	} else {
		ret = 0;
	}

	free(fentry_dig);
	free(file_digest);

	return ret;
}

static int
qcheck_process_contents(q_vdb_pkg_ctx *pkg_ctx, struct qcheck_opt_state *state)
{
	const char *catname = pkg_ctx->cat_ctx->name;
	const char *pkgname = pkg_ctx->name;

	int fd_contents;
	FILE *fp_contents, *fp_contents_update, *fp_contents_modes, *fp_contents_attrs_pax, *fp_contents_attrs_caps;
	size_t num_files, num_files_ok, num_files_unknown, num_files_ignored;
	FILE *fp_contents_digests_sha1, *fp_contents_digests_sha256, *fp_contents_digests_sha512;

	char *buffer, *line;
	size_t linelen;
	struct stat st, cst;
	int cp_argc, cpm_argc;
	char **cp_argv, **cpm_argv;

	int entry_id;
	bool srch_dig;
	int record_len;
	int ret_cmp;

	bool chk_mode = qcheck_state->chk_mode;
	bool chk_sha_digests = qcheck_state->chk_sha_digests;
	bool chk_attrs_pax = qcheck_state->chk_attrs_pax;
	bool chk_attrs_caps = qcheck_state->chk_attrs_caps;

	fp_contents = fp_contents_update = fp_contents_modes = fp_contents_attrs_pax = fp_contents_attrs_caps = NULL;
	fp_contents_digests_sha1 = fp_contents_digests_sha256 = fp_contents_digests_sha512 = NULL;

	/* Open contents */
	fd_contents = q_vdb_pkg_openat(pkg_ctx, "CONTENTS", O_RDONLY|O_CLOEXEC, 0);
	if (fd_contents == -1)
		return EXIT_SUCCESS;
	if (fstat(fd_contents, &cst)) {
		close(fd_contents);
		return EXIT_SUCCESS;
	}
	if ((fp_contents = fdopen(fd_contents, "r")) == NULL) {
		close(fd_contents);
		return EXIT_SUCCESS;
	}

	/* Open contents_update, if needed */
	num_files = num_files_ok = num_files_unknown = num_files_ignored = 0;
	qcprintf("%sing %s%s/%s%s ...\n",
		(state->qc_update ? "Updat" : "Check"),
		GREEN, catname, pkgname, NORM);
	if (state->qc_update) {
		fp_contents_update = q_vdb_pkg_fopenat_rw(pkg_ctx, "CONTENTS~");
		if (fp_contents_update == NULL) {
			fclose(fp_contents);
			warnp("unable to fopen(%s/%s, w)", pkgname, "CONTENTS~");
			return EXIT_FAILURE;
		}
	}

	/* Open contents_modes */
	if (verbose)
		qcprintf("%s%s/%s%s Opening modes-file\n",
			RED, catname, pkgname, NORM);
	fp_contents_modes = q_vdb_pkg_fopenat_ro(pkg_ctx, "CONTENTS_MODES");
	if (chk_mode) {
		/* Find failures */
		if (fp_contents_modes == NULL) {
			chk_mode = false;
			if (verbose)
				qcprintf("%s%s/%s%s No modes recorded, skipping modes check\n",
					RED, catname, pkgname, NORM);
		} else {
			if (verbose)
				qcprintf("%s%s/%s%s Found recorded modes, checking\n",
					RED, catname, pkgname, NORM);
		}
	}

	/* Open contents_digests_* */
	if (verbose)
		qcprintf("%s%s/%s%s Opening digests-files\n",
			RED, catname, pkgname, NORM);
	fp_contents_digests_sha1 = q_vdb_pkg_fopenat_ro(pkg_ctx, "CONTENTS_DIGESTS_SHA1");
	fp_contents_digests_sha256 = q_vdb_pkg_fopenat_ro(pkg_ctx, "CONTENTS_DIGESTS_SHA256");
	fp_contents_digests_sha512 = q_vdb_pkg_fopenat_ro(pkg_ctx, "CONTENTS_DIGESTS_SHA512");
	if (chk_sha_digests) {
		/* Find failures */
		if (fp_contents_digests_sha1 == NULL && fp_contents_digests_sha256 == NULL && fp_contents_digests_sha512 == NULL) {
			chk_sha_digests = false;
			if (verbose)
				qcprintf("%s%s/%s%s No sha-digests recorded, skipping digests checks\n",
					RED, catname, pkgname, NORM);
		} else {
			if (verbose)
				qcprintf("%s%s/%s%s Found recorded sha-digests, checking\n",
					RED, catname, pkgname, NORM);
		}
	}

	/* Open contents_attrs_pax */
	if (verbose)
		qcprintf("%s%s/%s%s Opening pax-file\n",
			RED, catname, pkgname, NORM);
	fp_contents_attrs_pax = q_vdb_pkg_fopenat_ro(pkg_ctx, "CONTENTS_ATTRS_PAX");
	if (chk_attrs_pax) {
		/* Find failures */
		if (fp_contents_attrs_pax == NULL) {
			chk_attrs_pax = false;
			if (verbose)
				qcprintf("%s%s/%s%s No pax-markings recorded, skipping pax check\n",
					RED, catname, pkgname, NORM);
		} else {
			if (verbose)
				qcprintf("%s%s/%s%s Found recorded pax-markings, checking\n",
					RED, catname, pkgname, NORM);
		}
	}

	/* Open contents_attrs_caps */
	if (verbose)
		qcprintf("%s%s/%s%s Opening caps-file\n",
			RED, catname, pkgname, NORM);
	fp_contents_attrs_caps = q_vdb_pkg_fopenat_ro(pkg_ctx, "CONTENTS_ATTRS_CAPS");
	if (chk_attrs_caps) {
		/* Find failures */
		if (fp_contents_attrs_caps == NULL) {
			chk_attrs_caps = false;
			if (verbose)
				qcprintf("%s%s/%s%s No caps recorded, skipping caps check\n",
					RED, catname, pkgname, NORM);
		} else {
			if (verbose)
				qcprintf("%s%s/%s%s Found recorded caps, checking\n",
					RED, catname, pkgname, NORM);
		}
	}

	if (!state->chk_config_protect) {
		makeargv(config_protect, &cp_argc, &cp_argv);
		makeargv(config_protect_mask, &cpm_argc, &cpm_argv);
	}

	entry_id = 0;
	buffer = line = NULL;
	while (getline(&line, &linelen, fp_contents) != -1) {
		/* In this loop we perform several tests.
		 * If a file fails a test, we do 'fail by continue'
		 * If a file succeeds all tests, num_files_ok is incremented
		 */
		contents_entry *entry;
		free(buffer);
		buffer = xstrdup(line);
		record_len = 0;
		srch_dig = true;
		ret_cmp = 0;

		entry_id++;
		entry = contents_parse_line(line);

		if (!entry)
			continue;

		/* run initial checks */
		++num_files;
		if (array_cnt(state->regex_arr)) {
			size_t n;
			regex_t *regex;
			array_for_each(state->regex_arr, n, regex)
				if (!regexec(regex, entry->name, 0, NULL, 0))
					break;
			if (n < array_cnt(state->regex_arr)) {
				--num_files;
				++num_files_ignored;
				continue;
			}
		}
		if (fstatat(pkg_ctx->cat_ctx->ctx->portroot_fd, entry->name + 1, &st, AT_SYMLINK_NOFOLLOW)) {
			/* make sure file exists */
			if (state->chk_afk) {
				if (errno == ENOENT)
					qcprintf(" %sAFK%s: %s\n", RED, NORM, entry->name);
				else
					qcprintf(" %sERROR (%s)%s: %s\n", RED, strerror(errno), NORM, entry->name);
			} else {
				--num_files;
				++num_files_ignored;
				if (state->qc_update)
					fputs(buffer, fp_contents_update);
			}
			continue;
		}

		/* Handle CONFIG_PROTECT-ed files */
		if (!state->chk_config_protect) {
			int i;
			/* If in CONFIG_PROTECT_MASK, handle like normal */
			for (i = 1; i < cpm_argc; ++i)
				if (strncmp(cpm_argv[i], entry->name, strlen(cpm_argv[i])) == 0)
					break;
			if (i == cpm_argc) {
				/* Not explicitly masked, so it's protected */
				for (i = 1; i < cp_argc; ++i)
					if (strncmp(cp_argv[i], entry->name, strlen(cp_argv[i])) == 0) {
						num_files_ok++;
						continue;
					}
			}
		}

		/* For certain combinations of flags and filetypes, a file
		 * won't get checks and should be ignored */
		if (!state->chk_mtime && entry->type == CONTENTS_SYM) {
			--num_files;
			++num_files_ignored;
			if (state->qc_update)
				fputs(buffer, fp_contents_update);

			continue;
		}

		/* Digest checks only work on regular files
		 * Note: We don't check for state->chk_hash when entering
		 * but rather in digest-check #3, because we only succeed
		 * tests/qcheck/list04.good if when chk_hash is false, we
		 * do check hashes, but only print mismatched digests as
		 * 'ignored file'. */
		if (entry->digest && S_ISREG(st.st_mode)) {
			/* Validate digest (handles MD5 / SHA1)
			 * Digest-check 1/3:
			 * Should we check digests? */
			char *f_digest;
			uint8_t hash_algo;
			switch (strlen(entry->digest)) {
				case 32: hash_algo = HASH_MD5; break;
				case 40: hash_algo = HASH_SHA1; break;
				default: hash_algo = 0; break;
			}

			if (!hash_algo) {
				if (state->chk_hash) {
					qcprintf(" %sUNKNOWN DIGEST%s: '%s' for '%s'\n", RED, NORM, entry->digest, entry->name);
					++num_files_unknown;
				} else {
					--num_files;
					++num_files_ignored;
					if (state->qc_update)
						fputs(buffer, fp_contents_update);
				}
				continue;
			}

			hash_cb_t hash_cb = state->undo_prelink ? hash_cb_prelink_undo : hash_cb_default;
			f_digest = (char *)hash_file_at_cb(pkg_ctx->cat_ctx->ctx->portroot_fd, entry->name + 1, hash_algo, hash_cb);

			/* Digest-check 2/3:
			 * Can we get a digest of the file? */
			if (!f_digest) {
				++num_files_unknown;
				free(f_digest);

				if (state->qc_update)
					fputs(buffer, fp_contents_update);

				if (verbose)
					qcprintf(" %sPERM %4o%s: %s\n", RED, (unsigned int)(st.st_mode & 07777), NORM, entry->name);

				continue;
			}

			/* Digest-check 3/3:
			 * Does the digest equal what portage recorded? */
			if (strcmp(entry->digest, f_digest) != 0) {
				if (state->chk_hash) {
					if (state->qc_update)
						fprintf(fp_contents_update, "obj %s %s %"PRIu64"\n", entry->name, f_digest, (uint64_t)st.st_mtime);

					const char *digest_disp;
					switch (hash_algo) {
						case HASH_MD5:	digest_disp = "MD5"; break;
						case HASH_SHA1:	digest_disp = "SHA1"; break;
						default: digest_disp = "UNK"; break;
					}

					qcprintf(" %s%s-DIGEST%s: %s", RED, digest_disp, NORM, entry->name);
					if (verbose)
						qcprintf(" (recorded '%s' != actual '%s')", entry->digest, f_digest);
					qcprintf("\n");
				} else {
					--num_files;
					++num_files_ignored;
					if (state->qc_update)
						fputs(buffer, fp_contents_update);
				}

				free(f_digest);
				continue;
			}

			free(f_digest);
		}

		/* Validate mtimes */
		if (state->chk_mtime && entry->mtime && entry->mtime != st.st_mtime) {
			qcprintf(" %sMTIME%s: %s", RED, NORM, entry->name);
			if (verbose)
				qcprintf(" (recorded '%"PRIu64"' != actual '%"PRIu64"')", (uint64_t)entry->mtime, (uint64_t)st.st_mtime);
			qcprintf("\n");

			/* Update mtime */
			if (state->qc_update) {
				if (entry->type == CONTENTS_SYM) {
					fprintf(fp_contents_update, "sym %s -> %s %"PRIu64"\n", entry->name, entry->sym_target, (uint64_t)st.st_mtime);
				} else {
					fprintf(fp_contents_update, "obj %s %s %"PRIu64"\n", entry->name, entry->digest, (uint64_t)st.st_mtime);
				}
			}

			continue;
		}

		/* Check mode, size 4+1 */
		if (chk_mode) {
			/* Get MODE from recorded CONTENTS_MODES */
			record_len = 4;
			char * fentry_mode = xcalloc(record_len+1, sizeof(char));

			if (get_recorded_meta(fentry_mode, fp_contents_modes, entry_id, record_len) == 1) {
				qcprintf("Error in CONTENTS_MODES, couldn't find entry: %s\n", entry->name);

				free(fentry_mode);
				continue;
			}

			/* We need a bigger buffer here, because filetype is part of stat_mode */
			char f_mode[7];
			snprintf(f_mode, 7, "%o", st.st_mode);

			/* Ignore 2 trailing chars of f_mode, because filetype is part of stat_mode */
			if (strcmp(f_mode+2, fentry_mode) != 0) {
				qcprintf(" %sMODE%s: %s", RED, NORM, entry->name);
				if (verbose)
					qcprintf(" ('%s' should be '%s')", f_mode+2, fentry_mode);
				qcprintf("\n");

				free(fentry_mode);
				continue;
			}

			free(fentry_mode);
		}

		/* Check digests */
		if (chk_sha_digests && srch_dig && fp_contents_digests_sha1 != NULL) {
			ret_cmp = cmp_recorded_digest(fp_contents_digests_sha1, entry_id, entry->name, "SHA1");
			if (ret_cmp == 0) /* Success */
				srch_dig = false; /* No need to try other digest types */
			else if (ret_cmp == -1)
				continue;
		}
		if (chk_sha_digests && srch_dig && fp_contents_digests_sha256 != NULL) {
			ret_cmp = cmp_recorded_digest(fp_contents_digests_sha256, entry_id, entry->name, "SHA256");
			if (ret_cmp == 0) /* Success */
				srch_dig = false; /* No need to try other digest types */
			else if (ret_cmp == -1)
				continue;
		}
		if (chk_sha_digests && srch_dig && fp_contents_digests_sha512 != NULL) {
			ret_cmp = cmp_recorded_digest(fp_contents_digests_sha512, entry_id, entry->name, "SHA512");
			if (ret_cmp == 0) /* Success */
				srch_dig = false; /* No need to try other digest types */
			else if (ret_cmp == -1)
				continue;
		}

		/* Check pax-markings, size 5+1 */
		if (chk_attrs_pax) {
			/* Get PAX from recorded CONTENTS_ATTRS_PAX */
			record_len = 5;
			char * fentry_pax = xcalloc(record_len+1, sizeof(char));

			if (get_recorded_meta(fentry_pax, fp_contents_attrs_pax, entry_id, record_len) == 1) {
				qcprintf("Error in CONTENTS_ATTRS_PAX, couldn't find entry: %s\n", entry->name);

				free(fentry_pax);
				continue;
			}

			size_t length = record_len;
			char buf[6] = "";
			char tmp1[6] = "0";
			char tmp2[6] = "00";
			char tmp3[6] = "000";
			char tmp4[6] = "0000";
			char f_pax[6] = "00000";

			if(!(getxattr(entry->name, "user.pax.flags", buf, length) == -1)) {
				int len = (int)strlen(buf);
				if (len == record_len) {
					strncpy(f_pax, buf, record_len);
				} else if (len == 4) {
					strncat(tmp1, buf, 5);
					strncpy(f_pax, tmp1, record_len);
				} else if (len == 3) {
					strncat(tmp2, buf, 4);
					strncpy(f_pax, tmp2, record_len);
				} else if (len == 2) {
					strncat(tmp3, buf, 3);
					strncpy(f_pax, tmp3, record_len);
				} else if (len == 1) {
					strncat(tmp4, buf, 2);
					strncpy(f_pax, tmp4, record_len);
				}
				f_pax[record_len] = '\0';
			} else {
				free(fentry_pax);
				continue;
			}

			/* Compare record vs actual, and print messages if they differ */
			if (strcmp(fentry_pax, f_pax) != 0) {
				qcprintf(" %sPAX%s: %s", RED, NORM, entry->name);
				if (verbose)
					qcprintf(" ('%s' should be '%s')", f_pax, fentry_pax);
				qcprintf("\n");
			} else {
				free(fentry_pax);
				continue;
			}

			free(fentry_pax);
		}

		/* Check POSIX-capabilities, size 16+1 */
		if (chk_attrs_caps) {
			/* Get CAPS from recorded CONTENTS_ATTRS_CAPS */
			record_len = 16;
			char * fentry_caps = xcalloc(record_len+1, sizeof(char));

			if (get_recorded_meta(fentry_caps, fp_contents_attrs_caps, entry_id, record_len) == 1)
				qcprintf("Error in CONTENTS_ATTRS_PAX, couldn't find entry: %s\n", entry->name);
				free(fentry_caps);
				continue;
			}

			size_t length = 20;
			unsigned char buf[20+1] = "";
			char f_caps[16+1] = "0000000000000000";

			/* Take the xattr value as string and process it */
			if(!(getxattr(entry->name, "security.capability", buf, length) == -1)) {
				long tmp = 0;
				long res = 0;

				/* Grab bytes 4 through 8 from xattr value */
				for (int i = 4; i < 8; ++i) {
					/* Convert those bytes to a long */
					if (tmp == 0)
						tmp = 1;
					else
						tmp = tmp*256;

					res = res + (((int) buf[i]) * tmp);
				}

				/* Convert long from dec to 16-pos hex string */
				snprintf(f_caps, record_len+1, "%016lx", res);
			} else {
				free(fentry_caps);
				continue;
			}

			/* Compare record vs actual, and print messages if they differ */
			if (strcmp(fentry_caps, f_caps) != 0) {
				qcprintf(" %sCAPS%s: %s", RED, NORM, entry->name);
				if (verbose)
					qcprintf(" ('%s' should be '%s')", f_caps, fentry_caps);
				qcprintf("\n");
			} else {
				free(fentry_caps);
				continue;
			}

			free(fentry_caps);
		}

		/* Success! */
		if (state->qc_update)
			fputs(buffer, fp_contents_update);

		num_files_ok++;
	}
	free(line);
	free(buffer);

	if (chk_mode) {
		fclose(fp_contents_modes);
	}
	if (chk_sha_digests) {
		if (fp_contents_digests_sha1 != NULL)
			fclose(fp_contents_digests_sha1);
		if (fp_contents_digests_sha256 != NULL)
			fclose(fp_contents_digests_sha256);
		if (fp_contents_digests_sha512 != NULL)
			fclose(fp_contents_digests_sha512);
	}
	if (chk_attrs_pax) {
		fclose(fp_contents_attrs_pax);
	}
	if (chk_attrs_caps) {
		fclose(fp_contents_attrs_caps);
	}

	if (!state->chk_config_protect) {
		freeargv(cp_argc, cp_argv);
		freeargv(cpm_argc, cpm_argv);
	}

	if (state->qc_update) {
		if (fchown(fd_contents, cst.st_uid, cst.st_gid)) {
			/* meh */;
		}
		if (fchmod(fd_contents, cst.st_mode)) {
			/* meh */;
		}
		fclose(fp_contents_update);
		if (renameat(pkg_ctx->fd, "CONTENTS~", pkg_ctx->fd, "CONTENTS"))
			unlinkat(pkg_ctx->fd, "CONTENTS~", 0);
		if (!verbose)
			return EXIT_SUCCESS;
	}

	if (fd_contents != -1)
		close(fd_contents);
	if (fp_contents != NULL)
		fclose(fp_contents);
	if (fp_contents_update != NULL)
		fclose(fp_contents_update);

	if (state->bad_only && num_files_ok != num_files) {
		if (verbose)
			printf("%s/%s:%s\n", catname, pkgname, pkg_ctx->slot);
		else {
			depend_atom *atom = NULL;
			char *buf;
			xasprintf(&buf, "%s/%s", catname, pkgname);
			if ((atom = atom_explode(buf)) != NULL) {
				printf("%s/%s-%s\n", catname, atom->PN, atom->PV);
				atom_implode(atom);
			} else {
				printf("%s/%s:%s\n", catname, pkgname, pkg_ctx->slot);
			}
			free(buf);
		}
	}
	qcprintf("  %2$s*%1$s %3$s%4$zu%1$s out of %3$s%5$zu%1$s file%6$s are good",
		NORM, BOLD, BLUE, num_files_ok, num_files,
		(num_files > 1 ? "s" : ""));
	if (num_files_unknown)
		qcprintf(" (Unable to digest %2$s%3$zu%1$s file%4$s)",
			NORM, BLUE, num_files_unknown,
			(num_files_unknown > 1 ? "s" : ""));
	if (num_files_ignored)
		qcprintf(" (%2$s%3$zu%1$s file%4$s ignored)",
			NORM, BLUE, num_files_ignored,
			(num_files_ignored > 1 ? "s were" : " was"));
	qcprintf("\n");

	if (num_files_ok != num_files)
		return EXIT_FAILURE;
	else
		return EXIT_SUCCESS;
}

static int
qcheck_cb(q_vdb_pkg_ctx *pkg_ctx, void *priv)
{
	struct qcheck_opt_state *state = priv;
	const char *catname = pkg_ctx->cat_ctx->name;
	const char *pkgname = pkg_ctx->name;
	bool showit = false;

	/* see if this cat/pkg is requested */
	if (array_cnt(state->atoms)) {
		char *buf;
		size_t i;
		depend_atom *qatom, *atom;

		xasprintf(&buf, "%s/%s", catname, pkgname);
		qatom = atom_explode(buf);
		array_for_each(state->atoms, i, atom)
			if (atom_compare(atom, qatom) == EQUAL) {
				showit = true;
				break;
			}
		atom_implode(qatom);
		free(buf);
	} else
		showit = true;

	return showit ? qcheck_process_contents(pkg_ctx, priv) : 0;
}

int qcheck_main(int argc, char **argv)
{
	size_t i;
	int ret;
	DECLARE_ARRAY(regex_arr);
	depend_atom *atom;
	DECLARE_ARRAY(atoms);
	struct qcheck_opt_state state = {
		.atoms = atoms,
		.regex_arr = regex_arr,
		.bad_only = false,
		.qc_update = false,
		.chk_afk = true,
		.chk_hash = true,
		.chk_mtime = true,
		.chk_config_protect = true,
		.undo_prelink = false,
	};

	while ((ret = GETOPT_LONG(QCHECK, qcheck, "")) != -1) {
		switch (ret) {
		COMMON_GETOPTS_CASES(qcheck)
		case 's': {
			regex_t regex;
			xregcomp(&regex, optarg, REG_EXTENDED|REG_NOSUB);
			xarraypush(regex_arr, &regex, sizeof(regex));
			break;
		}
		case 'u': state.qc_update = true; break;
		case 'A': state.chk_afk = false; break;
		case 'B': state.bad_only = true; break;
		case 'H': state.chk_hash = false; break;
		case 'T': state.chk_mtime = false; break;
		case 'P': state.chk_config_protect = false; break;
		case 'p': state.undo_prelink = prelink_available(); break;
		}
	}

	argc -= optind;
	argv += optind;
	for (i = 0; i < (size_t)argc; ++i) {
		atom = atom_explode(argv[i]);
		if (!atom)
			warn("invalid atom: %s", argv[i]);
		else
			xarraypush_ptr(atoms, atom);
	}

	ret = q_vdb_foreach_pkg_sorted(qcheck_cb, &state);
	{
		void *regex;
		array_for_each(regex_arr, i, regex)
			regfree(regex);
	}
	xarrayfree(regex_arr);
	array_for_each(atoms, i, atom)
		atom_implode(atom);
	xarrayfree_int(atoms);
	return ret;
}

#else
DEFINE_APPLET_STUB(qcheck)
#endif
