import json
import re
import math
import random
import numpy as np
from tqdm import tqdm
from random import sample
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

def read_from_test(lang = 'java'):
    python_dir = "/home/yangkang/container_data/Pooling/Parser/pythonV5_0720/python/"
    java_dir = "/home/yangkang/container_data/Pooling/Parser/java_0725/java/"

    if lang == 'java':
        _dir_ = java_dir
    else:
        _dir_ = python_dir

    filenames = {
        'src_test': _dir_ + 'test.token.code',
        'tgt_test': _dir_ + 'test.token.nl',
        'guid_test': _dir_ + 'test.token.guid',
        'fl_test': _dir_ + 'fl/',
        'dp_test': _dir_ + 'dp/',
        'ast_test': _dir_ + 'ast/',
        'adj_test': _dir_ + 'adjacency/',
    }



    with open(filenames['src_test']) as f:
        src_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['src_test']))]

    with open(filenames['tgt_test']) as f:
        tgt_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['tgt_test']))]

    with open(filenames['guid_test']) as f:
        guid_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['guid_test']))]

    return  src_test, tgt_test, guid_test, filenames

def read_files(lang='java'):
    from java_select_if_loop_struc import read_source_files
    import numpy as np
    # 读取 用于训练的 预处理好的 testset
    src_test, tgt_test, guid_test, filenames = read_from_test(lang=lang)
    # 读取 缘是的 未经处理的 dataset 用于抽取 if for while
    dataset = read_source_files(lang=lang)

    fl_dir = filenames['fl_test']
    dp_dir = filenames['dp_test']
    ast_dir = filenames['ast_test']
    adj_dir = filenames['adj_test']
    assert len(src_test) == len(tgt_test) == len(guid_test)

    # 选择出来的 testset idx
    # from util_ahead_java_V1 import read_source_files
    # dataset = read_source_files()
    from java_select_if_loop_struc import get_info_if, get_info_for_while


    # selected_idx_if, if_in_src, if_in_tgt, summary_text_all = get_info_if(dataset['src_test'], dataset['tgt_test'])
    # selected_idx_loop, summary_text_all = get_info_for_while(dataset['src_test'], dataset['tgt_test'])
    # selected = list(set(selected_idx_if + selected_idx_loop))
    # python 1083 923 => 1947
    # java   1031 749 => 1628
    if lang == 'java':
        selected = sample(range(8714), 2000)
    else:
        selected = sample(range(18502), 2300)

    sorted_selected = sorted(selected)
    # sorted_selected, guid_test
    save_selected_guid_data(sorted_selected, src_test, tgt_test, guid_test, lang)
    return src_test, tgt_test, guid_test, filenames, dataset, sorted_selected

def get_cases_for_rpe():



    return 0

def get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc = 'fl', factor=0.1):
#     struc = ['fl', 'dp', 'ast', 'adj']

    fl_dir = filenames['fl_test']
    dp_dir = filenames['dp_test']
    ast_dir = filenames['ast_test']
    adj_dir = filenames['adj_test']
    # assert len(src_test) == len(tgt_test) == len(guid_test)
    #
    # # 选择出来的 testset idx
    # from util_ahead_java_V1 import get_info_if, get_info_for_while
    #
    # selected_idx_if, if_in_src, if_in_tgt, summary_text_all = get_info_if(dataset['src_test'], dataset['tgt_test'])
    # selected_idx_loop, summary_text_all = get_info_for_while(dataset['src_test'], dataset['tgt_test'])
    # selected = list(set(selected_idx_if + selected_idx_loop))
    #
    # sorted_selected = sorted(selected)
    # sorted_selected, guid_test
    # save_selected_guid_data(sorted_selected, src_test, tgt_test, guid_test)

    sample_exes = []
    # for i in selected:
    for i in sorted_selected:
        guid = guid_test[i]
    # for idx, guid in enumerate(guid_test):
    #     break
        # pass
        if struc == 'fl':
            temp_fl = np.load(fl_dir + '{}.npy.npz'.format(guid))
            matrix =  temp_fl.f.arr_0
        if struc == "dp":
            temp_dp = np.load(dp_dir + '{}.npy.npz'.format(guid))
            matrix =  temp_dp.f.arr_0
        if struc == "ast":
            temp_ast = np.load(ast_dir + '{}.npy.npz'.format(guid))
            matrix =  temp_ast.f.arr_0
        if struc == "adj":
            temp_adj = np.load(adj_dir + '{}.npy.npz'.format(guid))
            matrix =  temp_adj.f.arr_0

            # 从各个 AST的机构矩阵中 采样一些边
            # 输入： matrix 、 src 、
            # 输出： index、guid、label、edge_pair(index)、edge_pair(token)

        sample_ex = sample_from_mat(matrix, src_test[i], guid, factor=factor)
        sample_exes.append(sample_ex)
    count_examples(sample_exes)
    return sample_exes

# matrix, src_token = fl, src_test[i]
def sample_from_mat(matrix, src_token, guid, factor):
    tokens = src_token.split()
    assert len(matrix) == len(tokens)
    true_index_pair = []
    true_token_pair = []
    false_index_pair = []
    false_token_pair = []
    # 遍历 矩阵的每一行
    for i, col in enumerate(matrix):
        # 正样本采样，找到为true的列的index
        true_index = list(np.where(col==True)[0])
        # 除去对角线上的元素就是 需要的token pair的index
        true_j_list = [index for index in true_index if index != i]

        # 负样本采样，找到为false的列的index
        false_index = list(np.where(col==False)[0])

        # 有效采样的样本数目 为 正负pair 中最小的那一个的长度
        num = len(true_j_list) if len(true_j_list) < len(false_index) else len(false_index)

        # true 的个数比 false 多，负样本就得采样
        if len(true_j_list) < len(false_index):
            # num = len(true_j_list)
            false_j_list = sample(false_index, num)
        # false 的个数比 true 多，正样本就得采样
        if len(true_j_list) >= len(false_index):
            # num = len(false_index)
            true_j_list = sample(true_j_list, num)
            false_j_list = false_index
        # 防 assertError 的 bug
        # if false_j_list == [] or true_j_list == []:
        #     continue
        assert len(true_j_list) == len(false_j_list)
        for idx in range(len(true_j_list)):
        # for j in true_j_list:
            j_true = true_j_list[idx]
            j_false = false_j_list[idx]
            # 如果两个 token 相同则忽略
            if tokens[i] != tokens[j_true]:
                true_index_pair.append((i,j_true))
                true_token_pair.append((tokens[i], tokens[j_true]))

                false_index_pair.append((i,j_false))
                false_token_pair.append((tokens[i], tokens[j_false]))

    assert len(true_index_pair) == len(true_token_pair) == len(false_index_pair) == len(false_token_pair)

    l = len(true_index_pair)
    temp = list(range(l))

    selected = sample(temp, math.ceil(l * factor))
    selected_true_index_pair = [true_index_pair[i]  for i in selected]
    selected_true_token_pair = [true_token_pair[i]  for i in selected]
    selected_false_index_pair= [false_index_pair[i] for i in selected]
    selected_false_token_pair= [false_token_pair[i] for i in selected]

    sample_ex = {
        "guid":guid,
        # "true_index_pair":true_index_pair,
        # "true_token_pair":true_token_pair,
        # "false_index_pair":false_index_pair,
        # "false_token_pair":false_token_pair,

        "true_index_pair":selected_true_index_pair,
        "true_token_pair":selected_true_token_pair,
        "false_index_pair":selected_false_index_pair,
        "false_token_pair":selected_false_token_pair,

        "length":len(selected_true_index_pair)

    }

    return sample_ex
    # return true_index_pair, true_token_pair, false_index_pair, false_token_pair

def count_examples(examples):
    from random import sample
    length = []

    for ex in examples:

        length.append(ex['length'])

    print("totally {} cases".format(sum(length)))

def save_struc_prob_data(file_dir, examples):

    import numpy as np
    np.save('JAVA/fl.npy', fl_examples)
    np.save('JAVA/fl.npy', dp_examples)
    np.save('JAVA/fl.npy', ast_examples)

    return

def save_selected_guid_data(selected, src_test, tgt_test, guid_test, lang='java'):
    # 将selected 的guid 的cases src tgt guid 单独做成 test(probe) dataset，方便后续的 inference
    if lang == 'java':
        subtk_file_dir = './JAVA/selected_random/'
    else:
        subtk_file_dir = './PYTHON/selected_random/'
    key = 'probe_random_rpe'
    # selected_src, selected_guid, selected_tgt = [], [], []
    selected_src = [src_test[i] for i in selected]
    selected_guid = [guid_test[i] for i in selected]
    selected_tgt = [tgt_test[i] for i in selected]

    string_src, string_guid, string_tgt = [],[],[]
    assert len(selected_tgt) == len(selected_guid) == len(selected_src)
    for i  in range(len(selected_tgt)):
        string_src.append(selected_src[i] + '\n')
        string_tgt.append(selected_tgt[i] + '\n')
        string_guid.append(selected_guid[i] + '\n')


    with open(subtk_file_dir + '{}.token.code'.format(key), 'w', encoding='utf8') as f:
        with open(subtk_file_dir + '{}.token.guid'.format(key), 'w', encoding='utf8') as g:
            with open(subtk_file_dir + '{}.token.nl'.format(key), 'w', encoding='utf8') as h:
                f.writelines(string_src)
                g.writelines(string_guid)
                h.writelines(string_tgt)

    print("Done")


    return 0


if __name__ == '__main__':

    print("OK")
    lang = 'java'
    # lang = 'python'
    src_test, tgt_test, guid_test, filenames, dataset, sorted_selected = read_files(lang=lang)
    print("***" * 20)
    if lang == 'java':
        fl_examples =  get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc='fl', factor=0.1)
        dp_examples =  get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc= "dp", factor=0.033)
        ast_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc= "ast", factor=0.02)
        adj_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc= "adj", factor=0.0115)

        np.save('JAVA/random_fl.npy', fl_examples)
        np.save('JAVA/random_dp.npy', dp_examples)
        np.save('JAVA/random_ast.npy', ast_examples)
        np.save('JAVA/random_adj.npy', adj_examples)
    else:
        fl_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
                                            struc='fl', factor=0.16)
        dp_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
                                            struc="dp", factor=0.072)
        ast_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
                                             struc="ast", factor=0.026)
        adj_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
                                             struc="adj", factor=0.017)

        np.save('PYTHON/random_fl.npy', fl_examples)
        np.save('PYTHON/random_dp.npy', dp_examples)
        np.save('PYTHON/random_ast.npy', ast_examples)
        np.save('PYTHON/random_adj.npy', adj_examples)


    print("OK")

