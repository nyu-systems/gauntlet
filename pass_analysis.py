import os
import glob
import shutil
import argparse
import subprocess
from pathlib import Path

import z3_p4.util as util

# configure logging
import logging
logging.basicConfig(format="%(levelname)s:%(message)s",
                    level=logging.INFO)
log = logging.getLogger(__name__)
PARSER = argparse.ArgumentParser()
PARSER.add_argument("-i", "--p4_input", dest="p4_input",
                    default="p4c/testdata/p4_16_samples", help="A P4 file or path to a "
                    "directory which contains P4 files.")

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
P4_BIN = FILE_DIR + "/p4c/build/p4c-bm2-ss"


def prune_files(p4_dmp_dir):
    p4_prune_dir = f"{p4_dmp_dir}/pruned"
    util.check_dir(p4_prune_dir)
    for p4_file in glob.glob(f"{p4_dmp_dir}/*.p4"):
        sed_cmd = "sed -r "
        sed_cmd += "\':a; s%(.*)/\\*.*\\*/%\\1%; ta; /\\/\\*/ !b; N; ba\' "
        sed_cmd += f"{p4_file} "
        sed_cmd += " | sed -r \'/^\\s*$/d\' "
        sed_cmd += f"> {p4_prune_dir}/{os.path.basename(p4_file)}"
        log.debug(f"Removing comments and whitespace")
        log.debug(f"Command: {sed_cmd}")
        util.exec_process(sed_cmd)
    return p4_prune_dir


def diff_files(passes, pass_dir, p4_prune_dir, p4_file):

    p4_name = Path(os.path.basename(p4_file)).stem
    for index, p4_pass in enumerate(passes[1:]):
        pass_before = glob.glob(f"{p4_prune_dir}/*{passes[index]}*.p4")
        pass_after = glob.glob(f"{p4_prune_dir}/*{passes[index+1]}*.p4")
        if not(pass_before and pass_after):
            log.error(f"Could not find the P4 files for pass {p4_name}! "
                      "Some passes were not generated.")
            continue
        # pass_before = f"{p4_prune_dir}/{p4_base}-{passes[index]}.p4"
        # pass_after = f"{p4_prune_dir}/{p4_base}-{passes[index+1]}.p4"
        pass_before = pass_before[0]
        pass_after = pass_after[0]
        diff_dir = f"{pass_dir}/{p4_name}"
        util.check_dir(diff_dir)
        diff_file = f"{diff_dir}/{p4_name}_{p4_pass}.diff"
        diff_cmd = "diff -rupP "
        diff_cmd += "--label=\"before_pass\" --label=\"after_pass\" "
        diff_cmd += f"{pass_before} {pass_after}"
        diff_cmd += f"> {diff_file}"
        log.debug(f"Creating a diff of the file")
        log.debug(f"Command: {diff_cmd}")
        util.exec_process(diff_cmd)
        if os.stat(diff_file).st_size == 0:
            os.remove(diff_file)
        else:
            shutil.copyfile(pass_after,
                            f"{diff_dir}/{p4_name}_{p4_pass}.p4")
            shutil.copyfile(p4_file,
                            f"{diff_dir}/{p4_name}_original.p4")
    return util.EXIT_SUCCESS


def get_links_to_passes(pass_dir, p4_file):
    util.check_dir(pass_dir)
    p4_name = os.path.splitext(os.path.basename(p4_file))[0]
    passes = {}
    for p4_file in glob.glob(f"{pass_dir}/**/full_{p4_name}*.p4"):
        split_p4 = p4_file.split('/')
        passes.setdefault(split_p4[1], []).append(split_p4[2])

    if passes.keys():
        with open(f"{pass_dir}/{p4_name}_matches.txt", 'w+') as match_file:
            for key in passes.keys():
                match_file.write(f"{key} ###########\n")
                for p4_test in passes[key]:
                    src_dir = "https://github.com/fruffy/"
                    src_dir += "p4_tv/tree/master/"
                    src_dir += "p4_16_samples/"
                    match_file.write(f"{src_dir}{p4_test}\n")
    else:
        with open(f"{pass_dir}/no_passes.txt", 'a') as match_file:
            match_file.write(f"{p4_file}\n")


def list_passes(p4_file):
    p4_pass_cmd = f"{P4_BIN} -v "
    p4_pass_cmd += f"{p4_file} 2>&1 "
    p4_pass_cmd += "| sed -e \'/FrontEnd_0_/,$!d\' | "
    p4_pass_cmd += "sed -e \'/MidEndLast/q\' "
    log.debug(f"Grabbing passes with command {p4_pass_cmd}")
    output = subprocess.check_output(p4_pass_cmd, shell=True)
    passes = output.decode('ascii').strip().split('\n')
    return passes


def generate_p4_dump(p4_file, p4_dmp_dir):
    p4_cmd = f"{P4_BIN} "
    p4_cmd += "--top4 FrontEnd,MidEnd "
    p4_cmd += f"--dump {p4_dmp_dir} "
    p4_cmd += p4_file
    log.debug(f"Running dumps with command {p4_cmd}")
    util.exec_process(p4_cmd)


def analyse_p4_file(p4_file, pass_dir):
    log.info(f"Analysing {p4_file}")
    p4_dmp_dir = f"dumps"
    util.check_dir(p4_dmp_dir)
    passes = list_passes(p4_file)
    generate_p4_dump(p4_file, p4_dmp_dir)
    prune_dir = prune_files(p4_dmp_dir)
    err = diff_files(passes, pass_dir, prune_dir, p4_file)
    # util.del_dir(p4_dmp_dir)


def main():
    # Parse options and process argv
    args = PARSER.parse_args()
    p4_input = args.p4_input
    if (os.path.isfile(p4_input)):
        pass_dir = "single_passes"
        util.check_dir(pass_dir)
        open(f"{pass_dir}/no_passes.txt", 'w+')
        analyse_p4_file(p4_input, pass_dir)
        get_links_to_passes(pass_dir, p4_input)
    else:
        pass_dir = "passes"
        util.check_dir(pass_dir)
        open(f"{pass_dir}/no_passes.txt", 'w+')
        for p4_file in glob.glob(f"{p4_input}/*.p4"):
            analyse_p4_file(p4_file, pass_dir)
            get_links_to_passes(pass_dir, p4_file)


if __name__ == '__main__':
    main()
