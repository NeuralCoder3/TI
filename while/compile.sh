#! /bin/sh
#
# compile.sh
# Copyright (C) 2019 marcel <marcel@archpc>
#
# Distributed under terms of the MIT license.
#


ghc -O2 -main-is Main --make Main.hs -threaded
