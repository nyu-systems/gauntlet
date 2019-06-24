#!/bin/bash

# Install pip locally
export PATH+=$PATH:~/.local/bin
wget https://bootstrap.pypa.io/get-pip.py
python3 get-pip.py --user
rm get-pip.py

# Install z3 locally
pip3 install --upgrade --user z3-solver