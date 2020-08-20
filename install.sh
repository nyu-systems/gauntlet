#!/bin/bash

# exit when any command fails
set -e

# parse custom args
for ARGUMENT in "$@"
do

    KEY=$(echo $ARGUMENT | cut -f1 -d=)
    VALUE=$(echo $ARGUMENT | cut -f2 -d=)

    case "$KEY" in
            INSTALL_BMV2)              INSTALL_BMV2=${VALUE} ;;
            *)
    esac


done

# fetch submodules and update apt
git submodule update --init --recursive
sudo apt-get update

MODULE_DIR="$(pwd)/modules"

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
mkdir -p ${MODULE_DIR}/p4c/extensions
# only install bludgeon if we are not running in travis
if test -z $TRAVIS; then
     ln -sf ${MODULE_DIR}/bludgeon ${MODULE_DIR}/p4c/extensions/bludgeon
fi
ln -sf ${MODULE_DIR}/toz3 ${MODULE_DIR}/p4c/extensions/toz3
# build the p4 compiler
cd ${MODULE_DIR}/p4c
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

# only install the behavioral model if requested
if [ "$INSTALL_BMV2" == "ON" ]; then

# Install the behavioral model dependencies
sudo apt install -y automake \
    cmake \
    libjudy-dev \
    libgmp-dev \
    libpcap-dev \
    libboost-dev \
    libboost-test-dev \
    libboost-program-options-dev \
    libboost-system-dev \
    libboost-filesystem-dev \
    libboost-thread-dev \
    libevent-dev \
    libtool \
    flex \
    bison \
    pkg-config \
    g++ \
    libssl-dev \
    libnanomsg-dev \
    libthrift-dev \
    libgrpc-dev \
    thrift-compiler

# build the p4 compiler
cd ${MODULE_DIR}/behavioral-model
./autogen.sh
./configure
make
sudo make install
cd -
fi


