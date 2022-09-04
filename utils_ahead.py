
import re
from tqdm import tqdm
import subprocess
def count_file_lines(file_path):
    """
    Counts the number of lines in a file using wc utility.
    :param file_path: path to file
    :return: int, no of lines
    """
    num = subprocess.check_output(['wc', '-l', file_path])
    num = num.decode('utf-8').split(' ')
    return int(num[0])



def split_camelcase(camel_case_identifier):
# def split_camelcase(camel_case_identifier: str) -> List[str]:
    """
    Split camelCase identifiers.
    come from code transformer
    """
    if not len(camel_case_identifier):
        return []
    # split into words based on adjacent cases being the same
    result = []
    current = str(camel_case_identifier[0])
    prev_upper = camel_case_identifier[0].isupper()
    prev_digit = camel_case_identifier[0].isdigit()
    prev_special = not camel_case_identifier[0].isalnum()
    for c in camel_case_identifier[1:]:
        upper = c.isupper()
        digit = c.isdigit()
        special = not c.isalnum()
        new_upper_word = upper and not prev_upper
        new_digit_word = digit and not prev_digit
        new_special_word = special and not prev_special
        if new_digit_word or new_upper_word or new_special_word:
            result.append(current)
            current = c
        elif not upper and prev_upper and len(current) > 1:
            result.append(current[:-1])
            current = current[-1] + c
        elif not digit and prev_digit:
            result.append(current)
            current = c
        elif not special and prev_special:
            result.append(current)
            current = c
        else:
            current += c
        prev_digit = digit
        prev_upper = upper
        prev_special = special
    result.append(current)


    return result


def cap(line):
    # 判断一个字符串中是否包含大写字母
    # flag = False
    for x in line:
        if x.isupper():
            return True
    return False

# def split_identifier_into_parts(identifier):
# # def split_identifier_into_parts(identifier: str) -> List[str]:
#     """
#     Split a single identifier into parts on snake_case and camelCase
#     come from code transformer
#     """
#     snake_case = identifier.split("_")
#     results = []
#     identifier_parts = []  # type: List[str]
#     for i in range(len(snake_case)):
#         part = snake_case[i]
#         if len(part) > 0 and cap(part):
#             identifier_parts.extend(split_camelcase(part))
#             # identifier_parts.extend(s.lower() for s in split_camelcase(part))
#     if len(identifier_parts) == 0:
#         # return [identifier]
#         return snake_case
#     return identifier_parts

def split_identifier_into_parts(identifier):
    """
    Split a single identifier into parts on snake_case and camelCase
    come from code transformer
    """
    snake_case = identifier.split("_")
    identifier_parts = []  # type: List[str]
    for i in range(len(snake_case)):

        part = snake_case[i]

        if len(part)>0:
            if not cap(part):
                identifier_parts.append(part)
            else:
                # identifier_parts.extend(split_camelcase(part))
                # identifier_parts.append(split_camelcase(part))
                split_parts = split_camelcase(part)
                lower_split_parts = [s.lower().strip() for s in split_parts]
                # identifier_parts.append(s.lower() for s in split_camelcase(part))
                identifier_parts.extend(lower_split_parts)

    return identifier_parts


class Tokens(object):
    """Special node type for walking Abstract Syntax Tree."""

    def __init__(self, words, source):
        self.tokens = words
        self.source = source

    def words(self):
        return self.tokens






def read_source_files():
    '''
        原始数据从 sgtrans 中读取
    '''
    _dir_ = '../DATA_RAW/sgtrans/Python/data/python/'
    # _dir_ = '/home/yangkang/container_data/Pooling/DATA_RAW/sgtrans/Java/data/java/'
    filenames = {

        'src_raw_train': _dir_ + 'train/originalcode',

        'src_raw_dev': _dir_ + 'dev/originalcode',

        'src_raw_test': _dir_ + 'test/originalcode',
    }


    with open(filenames['src_raw_train']) as f:
        sources_raw_train = [line.strip() for line in
                   tqdm(f, total=count_file_lines(filenames['src_raw_train']))]

    with open(filenames['src_raw_dev']) as f:
        sources_raw_dev = [line.strip() for line in
                   tqdm(f, total=count_file_lines(filenames['src_raw_dev']))]


    with open(filenames['src_raw_test']) as f:
        sources_raw_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['src_raw_test']))]

    print("raw dataread from 【sgtrans】! done !\n")
    return  sources_raw_train, sources_raw_dev, sources_raw_test


def read_frm_sgtrans():
    import numpy as np
    filenames = {
        'src_test': '/home/yangkang/container_data/Code/sgtrans/Python/data/python/test/code.original_subtoken',
        'tgt_test': '/home/yangkang/container_data/Code/sgtrans/Python/data/python/test/javadoc.original',

        'intok_test':'/home/yangkang/container_data/Code/sgtrans/Python/data/python/test/code.intoken',
        'instm_test':'/home/yangkang/container_data/Code/sgtrans/Python/data/python/test/code.instatement',
        'datafl_test':'/home/yangkang/container_data/Code/sgtrans/Python/data/python/test/dataflow_subtoken_v3.npy',
    }


    source_dataflow_sp = np.load(filenames['datafl_test'], allow_pickle=True)  # 读取


    with open(filenames['src_test']) as f:
        src_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['src_test']))]

    with open(filenames['tgt_test']) as f:
        tgt_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['tgt_test']))]


    with open(filenames['intok_test']) as f:
        intok_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['intok_test']))]

    with open(filenames['instm_test']) as f:
        instm_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['instm_test']))]
    return  src_test, tgt_test, intok_test, instm_test, source_dataflow_sp


def read_frm_ahead():
    import numpy as np
    filenames = {
        'src_test': '/home/yangkang/container_data/Pooling/Parser/python_0626/test.token.code',
        'src_train': '/home/yangkang/container_data/Pooling/Parser/python_0626/train.token.code',
        'src_dev': '/home/yangkang/container_data/Pooling/Parser/python_0626/dev.token.code',
        # 'src_test': '/home/yangkang/container_data/Code/sgtrans/Python/data/python/test/code.original_subtoken',
        'tgt_test': '/home/yangkang/container_data/Code/sgtrans/Python/data/python/test/javadoc.original',
        'tgt_train': '/home/yangkang/container_data/Code/sgtrans/Python/data/python/train/javadoc.original',
        'tgt_dev': '/home/yangkang/container_data/Code/sgtrans/Python/data/python/dev/javadoc.original',
                # / home / yangkang / container_data / Pooling / Parser / python_0626 /
        'intok_test':'/home/yangkang/container_data/Code/sgtrans/Python/data/python/test/code.intoken',
        'instm_test':'/home/yangkang/container_data/Code/sgtrans/Python/data/python/test/code.instatement',
        'datafl_test':'/home/yangkang/container_data/Code/sgtrans/Python/data/python/test/dataflow_subtoken_v3.npy',



    }


    source_dataflow_sp = np.load(filenames['datafl_test'], allow_pickle=True)  # 读取


    with open(filenames['src_test']) as f:
        src_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['src_test']))]


    with open(filenames['src_train']) as f:
        src_train = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['src_train']))]


    with open(filenames['src_dev']) as f:
        src_dev = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['src_dev']))]

    with open(filenames['tgt_test']) as f:
        tgt_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['tgt_test']))]


    with open(filenames['tgt_train']) as f:
        tgt_train = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['tgt_train']))]


    with open(filenames['tgt_dev']) as f:
        tgt_dev = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['tgt_dev']))]


    with open(filenames['intok_test']) as f:
        intok_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['intok_test']))]

    with open(filenames['instm_test']) as f:
        instm_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['instm_test']))]
    return  src_test,src_train,src_dev, tgt_test,tgt_train, tgt_dev, intok_test, instm_test, source_dataflow_sp



def read_src_and_tgt_files():
    _dir_ = '../DATA_RAW/sgtrans/Python/data/python/'
    # _dir_ = '../DATA_RAW/sgtrans/Java/data/java/'

    filenames = {
        'src_raw_test': _dir_ + 'test/originalcode',
        'tgt_raw_test': _dir_ + 'test/javadoc.original',
        'test_guid':'../DATA_RAW/SCRIPT_dataset/python/test.token.guid',
    }

    with open(filenames['src_raw_test']) as f:
        sources_raw_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['src_raw_test']))]

    with open(filenames['tgt_raw_test']) as f:
        targets_raw_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['tgt_raw_test']))]

    with open(filenames['test_guid']) as f:
        test_guid = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['test_guid']))]


    print("dataset read ! done !\n")
    assert len(test_guid) == len(targets_raw_test) == len(sources_raw_test)
    return  sources_raw_test, targets_raw_test, test_guid
    # return  sources_raw_train, sources_raw_dev, sources_raw_test, targets_raw_train, targets_raw_dev, targets_raw_test, test_guid



def python_tokenize(line):

    tokens = re.split('\.|\(|\)|\:| |;|,|!|=|[|]|', line)

    tokens = [t for t in tokens if t]
    temp = []
    for item in tokens:
        splt = split_identifier_into_parts(item)
        temp += splt
    return temp
    # return [t for t in temp if t.strip()]
    # return [t for t in tokens if t.strip()]




if __name__ == '__main__':
    # Parse cmdline args and setup environment
    identifier = 'goAhead_snake_cases_0ahsdAhks'
    tokens = python_tokenize(identifier)
    print(tokens)
    print("OK")

