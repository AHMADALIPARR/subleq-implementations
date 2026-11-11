#!/bin/sh
# Copyright (C) Ahmad <ahmedparr93@gmail.com>
# SPDX-License-Identifier: AGPL-3.0-only

# Install Ubuntu 24.04's gforth 0.7.3+dfsg-9build4.1 (the package this
# repository's Forth tests were run with) without using archive.ubuntu.com.
#
# GitHub-hosted runners fail to resolve azure.archive.ubuntu.com and
# archive.ubuntu.com, so apt-get and direct .deb URLs on those hosts fail.
# Building the upstream 0.7.3 tarball also fails: make dies in
# engine/prim-fast.i because gfgen's preforth falls back to /usr/bin/gforth,
# which is not on the runner yet.
#
# The .deb files are fetched from mirrors that are not under ubuntu.com.

set -eu

ver=0.7.3+dfsg-9build4.1

mirrors="
https://mirrors.edge.kernel.org/ubuntu
https://mirrors.kernel.org/ubuntu
http://ftp.osuosl.org/pub/ubuntu
https://ftp.fau.de/ubuntu
https://mirror.csclub.uwaterloo.ca/ubuntu
"

workdir=$(mktemp -d)
trap 'rm -rf "$workdir"' EXIT

fetch() {
  rel=$1
  dest=$2
  for mirror in $mirrors; do
    echo "fetch $mirror/$rel"
    if curl -fsSL --connect-timeout 20 --retry 5 --retry-delay 2 \
        --retry-all-errors -o "$dest" "$mirror/$rel"; then
      return 0
    fi
    rm -f "$dest"
  done
  echo "could not download $rel from any mirror" >&2
  return 1
}

ensure_deb() {
  pkg=$1
  rel=$2
  if dpkg -s "$pkg" >/dev/null 2>&1; then
    echo "$pkg already installed"
    return 0
  fi
  debname=$(basename "$rel")
  fetch "$rel" "$workdir/$debname"
  sudo DEBIAN_FRONTEND=noninteractive dpkg -i "$workdir/$debname"
}

ensure_deb libffi8 pool/main/libf/libffi/libffi8_3.4.6-1build1_amd64.deb
ensure_deb libltdl7 pool/main/libt/libtool/libltdl7_2.4.7-7build1_amd64.deb
ensure_deb emacsen-common pool/main/e/emacsen-common/emacsen-common_3.0.8build1_all.deb

for deb in \
  "gforth-common_${ver}_all.deb" \
  "gforth-lib_${ver}_amd64.deb" \
  "gforth_${ver}_amd64.deb"
do
  fetch "pool/universe/g/gforth/$deb" "$workdir/$deb"
done

sudo DEBIAN_FRONTEND=noninteractive dpkg -i \
  "$workdir/gforth-common_${ver}_all.deb" \
  "$workdir/gforth-lib_${ver}_amd64.deb" \
  "$workdir/gforth_${ver}_amd64.deb"

gforth --version
