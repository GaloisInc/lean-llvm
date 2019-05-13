#!/bin/bash
set -e

./build.sh

./dump_llvm $1
