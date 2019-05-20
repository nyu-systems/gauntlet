import os
import glob
import shutil

# configure logging
import logging
logging.basicConfig(format="%(levelname)s:%(message)s",
                    level=logging.INFO)
log = logging.getLogger(__name__)


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


def diff_files(p4_prune_dir, p4_file):
    passes = []
    with open("passes.txt") as f:
        passes = f.read().splitlines()

    for index, p4_pass in enumerate(passes[1:]):
        pass_before = glob.glob(f"{p4_prune_dir}/*{passes[index]}*.p4")
        pass_after = glob.glob(f"{p4_prune_dir}/*{passes[index+1]}*.p4")
        if not(pass_before and pass_after):
            return
        pass_dir = f"passes/{p4_pass}"
        diff_file = f"{pass_dir}/{p4_file}"
        check_dir(pass_dir)
        diff_cmd = "diff -rupP "
        diff_cmd += f"{pass_before[0]} {pass_after[0]}"
        diff_cmd += f"> {diff_file}"
        log.debug(f"Creating a diff of the file")
        log.debug(f"Command: {diff_cmd}")
        os.system(diff_cmd)
        if os.stat(diff_file).st_size == 0:
            os.remove(diff_file)


def main():

    p4_dir = "p4_16_samples"
    for p4_file in glob.glob(f"{p4_dir}/*.p4"):
        log.info(f"Analysing {p4_file}")
        p4_dmp_dir = f"dumps/{p4_file}"
        check_dir(p4_dmp_dir)
        p4_cmd = "p4c-bm2-ss "
        p4_cmd += "--top4 FrontEndLast,MidEnd "
        p4_cmd += f"--dump {p4_dmp_dir} "
        p4_cmd += p4_file
        log.debug(f"Running dumps with command {p4_cmd}")
        os.system(p4_cmd)
        prune_dir = prune_files(p4_dmp_dir)
        diff_files(prune_dir, os.path.basename(p4_file))
        shutil.rmtree(p4_dmp_dir)
    shutil.rmtree("dumps")


if __name__ == '__main__':
    main()
