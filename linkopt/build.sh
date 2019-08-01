#!/bin/sh
set -eux

clean () {
	cd ./xed
	./mfile.py clean
	cd ..

	rm -Rf libxed
}

build () {
	cd ./xed
	# Need to set ia32 or else mbuild adds -m64
	./mfile.py --host-cpu=ia32 --host-os=lin --extra-flags="-Oz -emit-llvm -target le32-unknown-nacl -nostdlibinc -isystem ../pdclib/include -isystem ../pdclib_platform/include"
	cd ..
	
	rm -Rf libxed
	mkdir libxed
	cd libxed
	ar x ../xed/obj/libxed.a
	cd ..

	
}

case "${1-}" in
	clean) clean ;;
	build) build ;;
	'') build ;;
	*) echo 'Specify "build" or "clean"' >&2 ;;
esac
