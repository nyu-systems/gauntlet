from pathlib import Path
import sys

FILE_DIR = Path.resolve(Path(__file__)).parent

# avoid annoying import errors...
sys.path.append(str(FILE_DIR) + "/..")

from p4z3.base import *
from p4z3.expressions import *
from p4z3.statements import *
from p4z3.callables import *
from p4z3.parser import *
