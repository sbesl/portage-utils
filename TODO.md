# Common

- unify match behavior:
	- default \*foo\*
	- -e foo
	- -r (-R ?) regexp foo.\*
- make default -e for apps like quse/qdepends?

- make set.c to array (xarray) instead of C-array (list)

- env vars only get expanded once, so this fails:<br>
  `ACCEPT_LICENSE="foo"`<br>
  `ACCEPT_LICENSE="${ACCEPT_LICENSE} bar"`<br>
  we end up getting just:<br>
  `ACCEPT_LICENSE=" bar"`

- tree\_foreach\_pkg should have variant that takes an atom (or just
  cat?) to reduce search space

- tree\_get\_atoms should return atoms iso string set, needs a rewrite
  to use foreach\_pkg and get\_atom

# Atoms

- only 32bit values are supported for revision (-r#)
- only 64bit values are supported in any individual version component
  foo-(1234)\_alpha(56789)
- these limits should not be an issue for all practical purposes

# qmerge

- dep resolver needs spanktastic love.
- needs safe deleting (merge in place rather than unmerge;merge)
- multiple binary repos (talk to zmedico)
- handle compressed Packages file (talk to zmedico)
- handle binary Packages file (talk to zmedico)
- gpg sign the packages file (before compression)
- binary vdb (sqlite) ... talk to zmedico
- remote vdb
- parallel fetch tbz2s
- check order of pkg\_{pre,post}{inst,rm} during install, unmerge, and upgrade
- env is not saved/restored between pkg\_{pre,post}inst (see portage and REPO\_LAYOUT\_CONF\_WARN)
- support installing via path to tbz2 package
- support TTL field in binpkgs file
- merge duplicate atoms on the CLI (`qmerge -Uq nano nano nano`)
- unmerging should clean out @world set
- test should work on local vdb (so TRAVIS can test it too)
- fixup lame misnaming of force\_download (--fetch/--force) actually
  not-forcing things

# qdepends

- add -S/-v/-R behavior like qlist #574934
- bring back -k?  (but seems solved by using qlist -IF%{SLOT} pkg)
- -Qt acts weird (if not, incorrect)
- -v should lookup whether packages are installed for || cases/colouring

# qpkg

- fix "would be freed" message when --pretend is *not* active
- add a verbose output that describes why a package is cleaned
	- newer binpkgs available
	- newer installed version available

# qgrep

- make it use standard xarray instead of its own buf\_list

# qlist
- have -F for use with -I so one can do things like print SLOT for
  package X

# quse
- make -v only print requested USE-flag when flags given

# qkeyword
- drop -c argument? it can be fully expressed using -p cat/

# qmanifest
- use openat in most places
- parse timestamps and print in local timezone

# qlop
- guestimate runtime based on best-matching pkg (e.g. with gcc)
- calculate or take some "smooth" factor just added on top of the
  guestimate alternative to current time jumping
- display excess time (+12:05) when overrunning guestimate to indicate
  longer run than last guestimate
