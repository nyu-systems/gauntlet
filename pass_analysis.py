import os
import glob
import shutil
import argparse

# configure logging
import logging
logging.basicConfig(format="%(levelname)s:%(message)s",
                    level=logging.INFO)
log = logging.getLogger(__name__)
PARSER = argparse.ArgumentParser()
PARSER.add_argument("-i", "--p4_input", dest="p4_input",
                    default="p4_16_samples", help="A P4 file or path to a "
                    "directory which contains P4 files.")

FAILURE = 1
SUCCESS = 0


def check_path(path):
    """Checks if a path is an actual directory and converts the input
        to an absolute path"""
    if not os.path.exists(path):
        msg = "{0} does not exist".format(path)
        raise argparse.ArgumentTypeError(msg)
    else:
        return os.path.abspath(os.path.expanduser(path))


def check_dir(directory):
    # create the folder if it does not exit
    if not directory == "" and not os.path.exists(directory):
        log.debug(f"Folder {directory} does not exist! Creating...")
        os.makedirs(directory)
        # preserve the original owner


def prune_files(p4_dmp_dir):
    p4_prune_dir = f"{p4_dmp_dir}/pruned"
    check_dir(p4_prune_dir)
    for p4_file in glob.glob(f"{p4_dmp_dir}/*.p4"):
        sed_cmd = "sed -r "
        sed_cmd += "\':a; s%(.*)/\\*.*\\*/%\\1%; ta; /\\/\\*/ !b; N; ba\' "
        sed_cmd += f"{p4_file} "
        sed_cmd += " | sed -r \'/^\\s*$/d\' "
        sed_cmd += f"> {p4_prune_dir}/{os.path.basename(p4_file)}"
        log.debug(f"Removing comments and whitespace")
        log.debug(f"Command: {sed_cmd}")
        os.system(sed_cmd)
    return p4_prune_dir


def diff_files(pass_dir, p4_prune_dir, p4_file):
    passes = []
    with open("passes.txt") as f:
        passes = f.read().splitlines()
    p4_base = os.path.splitext(os.path.basename(p4_file))[0]

    for index, p4_pass in enumerate(passes[1:]):
        pass_before = glob.glob(f"{p4_prune_dir}/*{passes[index]}*.p4")
        pass_after = glob.glob(f"{p4_prune_dir}/*{passes[index+1]}*.p4")
        if not(pass_before and pass_after):
            log.error(f"Could not find the P4 files! "
                      "Passes not generated.")
            return FAILURE
        # pass_before = f"{p4_prune_dir}/{p4_base}-{passes[index]}.p4"
        # pass_after = f"{p4_prune_dir}/{p4_base}-{passes[index+1]}.p4"
        pass_before = pass_before[0]
        pass_after = pass_after[0]
        diff_dir = f"{pass_dir}/{p4_pass}"
        diff_file = f"{diff_dir}/{p4_file}"
        check_dir(diff_dir)
        diff_cmd = "diff -rupP "
        diff_cmd += "--label=\"before_pass\" --label=\"after_pass\" "
        diff_cmd += f"{pass_before} {pass_after}"
        diff_cmd += f"> {diff_file}"
        log.debug(f"Creating a diff of the file")
        log.debug(f"Command: {diff_cmd}")
        os.system(diff_cmd)
        if os.stat(diff_file).st_size == 0:
            os.remove(diff_file)
        else:
            shutil.copyfile(pass_after, f"{diff_dir}/full_{p4_file}")
    return SUCCESS


def get_links_to_passes(pass_dir, p4_input):
    check_dir(pass_dir)
    p4_name = os.path.splitext(os.path.basename(p4_input))[0]
    passes = {}
    for p4_file in glob.glob(f"{pass_dir}/**/full_{p4_name}*.p4"):
        split_p4 = p4_file.split('/')
        passes.setdefault(split_p4[1], []).append(split_p4[2])
    with open(f"{pass_dir}/{p4_name}_matches.txt", 'w+') as match_file:
        for key in passes.keys():
            match_file.write(key + "###########\n")
            for p4_test in passes[key]:
                src_dir = "https://github.com/fruffy/p4_tv/tree/master/"
                src_dir += "p4_16_samples/"
                match_file.write(f"{src_dir}{p4_test}\n")


def analyse_p4_file(p4_file, pass_dir):
    log.info(f"Analysing {p4_file}")
    p4_dmp_dir = f"dumps"
    check_dir(p4_dmp_dir)
    p4_cmd = "p4c-bm2-ss "
    p4_cmd += "--top4 FrontEndLast,MidEnd "
    p4_cmd += f"--dump {p4_dmp_dir} "
    p4_cmd += p4_file
    log.debug(f"Running dumps with command {p4_cmd}")
    os.system(p4_cmd)
    prune_dir = prune_files(p4_dmp_dir)
    err = diff_files(pass_dir, prune_dir, os.path.basename(p4_file))
    shutil.rmtree(p4_dmp_dir)


def main():
    # Parse options and process argv
    args = PARSER.parse_args()
    p4_input = args.p4_input
    if (os.path.isfile(p4_input)):
        pass_dir = "single_passes"
        analyse_p4_file(p4_input, pass_dir)
        get_links_to_passes(pass_dir, p4_input)
    else:
        pass_dir = "passes"
        for p4_file in glob.glob(f"{p4_input}/*.p4"):
            analyse_p4_file(p4_file, pass_dir)
            get_links_to_passes(pass_dir, p4_file)


if __name__ == '__main__':
    main()
