import os
import subprocess
import shutil
import logging as log
from pathlib import Path

EXIT_SUCCESS = 0
EXIT_FAILURE = -1


def check_dir(directory):
    # create the folder if it does not exit
    if not directory == "" and not os.path.exists(directory):
        log.debug(f"Folder {directory} does not exist! Creating...")
        os.makedirs(directory)


def check_path(path):
    """Checks if a path is an actual directory and converts the input
        to an absolute path"""
    if not os.path.exists(path):
        msg = "{0} does not exist".format(path)
        raise argparse.ArgumentTypeError(msg)
    else:
        return os.path.abspath(os.path.expanduser(path))


def del_dir(directory):
    try:
        shutil.rmtree(directory)
    except OSError as e:
        log.error("Error: %s - %s." % (e.filename, e.strerror))


def exec_process(cmd, out_file=subprocess.STDOUT):
    log.debug("Executing %s " % cmd)
    if out_file is subprocess.STDOUT:
        result = subprocess.run(
            cmd.split(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.stdout:
            log.debug("Process output: %s" % result.stdout)
        if result.stderr and result.returncode != 0:
            log.error(result.stderr)
        return result
    err = out_file + ".err"
    out = out_file + ".out"
    with open(out, "w+") as f_out, open(err, "w+") as f_err:
        return subprocess.run(cmd.split(), stdout=f_out, stderr=f_err)
