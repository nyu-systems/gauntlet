FROM ubuntu:bionic
WORKDIR /home/

ENV DEPS python \
        python3 \
        python-pip \
        python3-pip

ENV P4C_DEPS bison \
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
            python-setuptools \
            libprotoc-dev \
            protobuf-compiler

ENV PIP_PACKAGES wheel \
                 z3-solver \
                 pytest

RUN apt update
RUN apt install -y $DEPS $P4C_DEPS
RUN pip3 install --user $PIP_PACKAGES
RUN git clone https://github.com/p4gauntlet/p4_tv && \
    cd /home/p4_tv && \
    git submodule update --init --recursive --remote && \
    mkdir p4c/extensions

# Grab the p4c-z3 compiler extension into the extension folder
RUN git clone https://github.com/p4gauntlet/toz3 p4c/extensions/toz3

# build p4c and p4c-toz3
RUN cd p4c && \
    mkdir -p build && \
    cd build && \
    cmake .. && \
    make -j `getconf _NPROCESSORS_ONLN` && \
    make install && \
    cd ../..

RUN cd p4c/extensions/toz3/ && \
    # link the compiler
    ln -sf /home/p4c/build/p4toz3 toz3
    cd ../../..

# done