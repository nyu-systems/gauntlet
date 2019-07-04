#!/bin/bash

# exit when any command fails
set -e

# fetch submodules
git submodule update --init --recursive --remote --merge

# Install pip locally
export PATH+=$PATH:~/.local/bin
wget https://bootstrap.pypa.io/get-pip.py
python3 get-pip.py --user
rm get-pip.py

# Install the p4 compiler
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

pip install --user pyroute2 ipaddr ply==3.8 scapy==2.4.0
cd p4c
mkdir -p build
cd build
cmake ..
make -j `getconf _NPROCESSORS_ONLN`
cd ../..

# Install z3 locally
pip3 install --upgrade --user z3-solver