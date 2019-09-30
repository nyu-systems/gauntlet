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
                 z3-solver

RUN apt update
RUN apt install -y $DEPS $P4C_DEPS
RUN pip3 install --user $PIP_PACKAGES
RUN git clone https://github.com/p4bughunt/p4_tv && \
    cd /home/p4_tv && \
    git submodule update --init --recursive --remote && \
    cd p4c && \
    mkdir -p build && \
    cd build && \
    cmake .. && \
    make -j `getconf _NPROCESSORS_ONLN` && \
    make install && \
    cd ../..
