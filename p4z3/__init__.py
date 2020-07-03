import os
import sys
FILE_DIR = os.path.dirname(os.path.abspath(__file__))

# avoid annoying import errors...
sys.path.append(FILE_DIR)

from p4z3.base import *
from p4z3.expressions import *
from p4z3.statements import *
from p4z3.parser import *
from p4z3.callables import *
