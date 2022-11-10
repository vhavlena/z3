#!/usr/bin/env sh

cd build/ && cmake ../ && make -j 4 test-noodler && ./test-noodler
