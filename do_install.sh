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
echo "Initializing submodules..."
git submodule update --init --recursive
sudo apt-get update

SRC_DIR="$(pwd)"
MODULE_DIR="$(pwd)/modules"

echo "Installing P4C dependencies..."

# Install pip and python
sudo apt install -y python3
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
                    pkg-config

# This only works on Ubuntu 18+
sudo apt install -y libprotoc-dev protobuf-compiler

# install python packages using pip
pip3 install --user wheel
pip3 install --user pyroute2 ipaddr ply scapy

# only install the behavioral model if requested
if [ "$INSTALL_BMV2" == "ON" ]; then
echo "Behavioral model install selected."

# Install the behavioral model dependencies
echo "Installing behavioral model dependencies."
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
    libgrpc-dev


echo "Installing thrift dependency."
# this only works on Ubuntu 19.10+...
if sudo apt install -y libthrift-dev ; then
    sudo apt install -y thrift-compiler
    echo "Installed thrift with apt."
else
# unfortunately we still have to install thrift the manual way...
    cd ${MODULE_DIR}/behavioral-model
    wget -N https://archive.apache.org/dist/thrift/0.13.0/thrift-0.13.0.tar.gz
    tar -xvf thrift-0.13.0.tar.gz
    cd thrift-0.13.0/
    ./bootstrap.sh
    ./configure --without-rs --without-nodejs
    make
    sudo make install
    sudo ldconfig
fi

pip3 install --user thrift==0.13.0

# build the behavioral model
echo "Installing behavioral model..."
cd ${MODULE_DIR}/behavioral-model
autoreconf -i # this is needed for some reason...
./autogen.sh
./configure
make
sudo make install
cd ${SRC_DIR}
fi


# grab the toz3 extension for the p4 compiler
mkdir -p ${MODULE_DIR}/p4c/extensions
# only install bludgeon if we are not running in travis
if test -z $TRAVIS; then
     ln -sf ${MODULE_DIR}/bludgeon ${MODULE_DIR}/p4c/extensions/bludgeon
     ln -sf ${MODULE_DIR}/pruner ${MODULE_DIR}/p4c/extensions/pruner
fi
ln -sf ${MODULE_DIR}/toz3 ${MODULE_DIR}/p4c/extensions/toz3

# build the p4 compiler
echo "Building P4C..."
cd ${MODULE_DIR}/p4c
mkdir -p build
cd build
cmake .. -DCMAKE_BUILD_TYPE=RelWithDebInfo
make -j `getconf _NPROCESSORS_ONLN`
cd ../..

echo "Installing Gauntlet Python dependencies..."
# Install z3 locally
pip3 install --upgrade --user z3-solver
# Pytests for tests
pip3 install --upgrade --user pytest
# Run tests in parallel
pip3 install --upgrade --user pytest-xdist
# Python 3.6 compatibility
pip3 install --upgrade --user dataclasses



echo "Gauntlet installation completed successfully."
