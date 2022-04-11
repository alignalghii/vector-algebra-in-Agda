#!/bin/bash

if test $# -eq 1;
	then
		prefix=$1;
		(
			cd $prefix;

			for fileName in *.agda;
				do
					sed -i "s/^\(module\|open import\) \($prefix\)\($\| \)/\1 \2.Base\3/; s/^\(module\|open import\) \($prefix\)\(\w\+\)/\1 \2.\3/;" $fileName;
					git mv $fileName `sed "s/^$prefix\(\w\+\)/\1/; s/^\($prefix\)\(\..*\)\?$/Base\2/;" <<< $fileName`;
			done;
		)
	else
		echo "Provide a prefix as a single argument" >&2;
		exit 1;
fi;
