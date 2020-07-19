#!/bin/bash

# exit when any command fails
set -e

# fetch submodules and update apt
git submodule update --init --recursive --remote --merge
sudo apt-get update


# Install pip and python
sudo apt install -y python3
sudo apt install -y python
sudo apt install -y python3-pip
sudo apt install -y python3-setuptools

# Install the p4 compiler dependencies
sudo apt install -y bison \
                    build-essential \
                    cmake \
                    git \
                    flex \
                    libboost-dev \
                    libboost-graph-dev \
                    libboost-iostreams-dev \
                    libfl-dev \
                    libgc-dev \
                    libgmp-dev \
                    pkg-config \
                    python-setuptools

# This only works on Ubuntu 18+
sudo apt install -y libprotoc-dev protobuf-compiler

# install python packages using pip
pip3 install --upgrade pip
pip3 install --user wheel
pip3 install --user pyroute2 ipaddr ply scapy

# grab the toz3 extension for the p4 compiler
mkdir -p p4c/extensions
# only install bludgeon if we are not running in travis
if test -z $TRAVIS; then
ln -s $(pwd)/bludgeon $(pwd)/p4c/extensions/bludgeon
fi
ln -s $(pwd)/toz3 $(pwd)/p4c/extensions/toz3
# build the p4 compiler
cd p4c
mkdir -p build
cd build
cmake .. -DCMAKE_BUILD_TYPE=RelWithDebInfo
make -j `getconf _NPROCESSORS_ONLN`
cd ../..

# Install z3 locally
pip3 install --upgrade --user z3-solver
pip3 install --upgrade --user pytest
# run tests in parallel
pip3 install --upgrade --user pytest-xdist
# Python 3.6 compatibility
pip3 install --upgrade --user dataclasses
