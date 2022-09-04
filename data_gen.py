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

# def get_cases_from_matrix():
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
    # file_dir_1 = "JAVA/fl_idx.txt"
    # file_dir_2 = "JAVA/fl_tok.txt"
    # # file_dir = "JAVA/dp.txt"
    # # file_dir = "JAVA/ast.txt"
    # with open(file_dir_1, 'w', encoding='utf8') as f:
    #     with open(file_dir_1, 'w', encoding='utf8') as f:
    #
    #     for ex in examples:
    #         guid = ex['guid']
    #         true_index_pair = ex['true_index_pair']
    #         true_token_pair = ex['true_token_pair']
    #         false_index_pair = ex['false_index_pair']
    #         false_token_pair = ex['false_token_pair']
    #         length = ex['length']
    #         for i in range(length):
    #             true_index_pair[i]
    #             false_index_pair[i]
    #             true_token_pair[i]
    #             false_token_pair[i]

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
    key = 'probe_random'
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


# def save_json(file, json_list):
#     file_dir = "JAVA/" + file
#     with open(file_dir, "w") as f:
#         for data in json_list:
#             line = json.dumps(data)
#             f.write(line + '\n')
#
# def read_json(file):
#     data = []
#     with open(file) as f:
#         lines = f.readlines()
#         for line in lines:
#             raw_line = json.loads(line)
#             data.append(raw_line)
#     return data


if __name__ == '__main__':
    # src_test, tgt_test, guid_test, filenames = read_from_test(lang='java')
    # 10916
    # fl_examples = get_cases_from_matrix(struc= "fl", factor=0.1)
    # print("***"*20)
    # 10281
    # dp_examples = get_cases_from_matrix(struc= "dp", factor=0.033)
    # print("***"*20)
    # 10561
    # ast_examples = get_cases_from_matrix(struc= "ast", factor=0.02)
    # np.save('JAVA/fl.npy', fl_examples)
    # np.save('JAVA/dp.npy', dp_examples)
    # np.save('JAVA/ast.npy', ast_examples)
    # fl_examples=np.load('JAVA/fl.npy',allow_pickle=True)
    # dp_examples=np.load('JAVA/dp.npy',allow_pickle=True)
    # ast_examples=np.load('JAVA/ast.npy',allow_pickle=True)
    # 10871 adj

    print("OK")
    # lang = 'java'
    lang = 'python'
    src_test, tgt_test, guid_test, filenames, dataset, sorted_selected = read_files(lang=lang)
    print("***" * 20)
    if lang == 'java':
        fl_examples =  get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc='fl', factor=0.25)
        dp_examples =  get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc= "dp", factor=0.1)
        ast_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc= "ast", factor=0.045)
        adj_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc= "adj", factor=0.027)
        # fl_examples =  get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc='fl', factor=0.1)
        # dp_examples =  get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc= "dp", factor=0.033)
        # ast_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc= "ast", factor=0.02)
        # adj_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected, struc= "adj", factor=0.0115)
        # tag = 'p-'
        np.save('JAVA/p-random_fl.npy', fl_examples)
        np.save('JAVA/p-random_dp.npy', dp_examples)
        np.save('JAVA/p-random_ast.npy', ast_examples)
        np.save('JAVA/p-random_adj.npy', adj_examples)
        # np.save('JAVA/random_fl.npy', fl_examples)
        # np.save('JAVA/random_dp.npy', dp_examples)
        # np.save('JAVA/random_ast.npy', ast_examples)
        # np.save('JAVA/random_adj.npy', adj_examples)
    else:
        fl_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
                                            struc='fl', factor=0.33)
        dp_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
                                            struc="dp", factor=0.15)
        ast_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
                                             struc="ast", factor=0.055)
        adj_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
                                             struc="adj", factor=0.035)

        # fl_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
        #                                     struc='fl', factor=0.16)
        # dp_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
        #                                     struc="dp", factor=0.072)
        # ast_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
        #                                      struc="ast", factor=0.026)
        # adj_examples = get_cases_from_matrix(src_test, tgt_test, guid_test, filenames, dataset, sorted_selected,
        #                                      struc="adj", factor=0.017)
        #
        np.save('PYTHON/p-random_fl.npy', fl_examples)
        np.save('PYTHON/p-random_dp.npy', dp_examples)
        np.save('PYTHON/p-random_ast.npy', ast_examples)
        np.save('PYTHON/p-random_adj.npy', adj_examples)
        # np.save('PYTHON/random_fl.npy', fl_examples)
        # np.save('PYTHON/random_dp.npy', dp_examples)
        # np.save('PYTHON/random_ast.npy', ast_examples)
        # np.save('PYTHON/random_adj.npy', adj_examples)


    print("OK")

    # java
    # totally 10916 cases
    # totally 10281 cases
    # totally 10561 cases
    # totally 10871 cases

    # python
    # totally 10240 cases
    # totally 10354 cases
    # totally 10124 cases
    # totally 10090 cases

#
# OK
# 100%|█████████████████████████████████| 18502/18502 [00:00<00:00, 609961.90it/s]
# 100%|████████████████████████████████| 18502/18502 [00:00<00:00, 1321824.81it/s]
# 100%|████████████████████████████████| 18502/18502 [00:00<00:00, 2459995.33it/s]
# 100%|████████████████████████████████| 55538/55538 [00:00<00:00, 1022070.95it/s]
# 100%|█████████████████████████████████| 18505/18505 [00:00<00:00, 908581.74it/s]
# 100%|█████████████████████████████████| 18502/18502 [00:00<00:00, 931978.01it/s]
# 100%|████████████████████████████████| 55538/55538 [00:00<00:00, 1765845.35it/s]
# 100%|████████████████████████████████| 18505/18505 [00:00<00:00, 1813872.30it/s]
# 100%|████████████████████████████████| 18502/18502 [00:00<00:00, 1674066.20it/s]
# dataset python read ! done !
#
# src_train set: 55538
# src_dev set: 18505
# src_test set: 18502
# tgt_train set: 55538
# tgt_dev set: 18505
# tgt_test set: 18502
# 【if】 in src : 9284
# 【if/or】 in tgt : 1809
# 【if】 in src and 【or/if】 in tgt: 1083
# 【All】 cases 18502
# 【for or while】 in src : 3926
# 3926 18502
# 【for/while】 in src and 【in/from】 in tgt: 923
# Done
# ************************************************************
# totally 10240 cases
# totally 10354 cases
# totally 10124 cases
# totally 10090 cases
# OK
#
# Process finished with exit code 0

#
# OK
# 100%|███████████████████████████████████| 8714/8714 [00:00<00:00, 285028.19it/s]
# 100%|██████████████████████████████████| 8714/8714 [00:00<00:00, 1048636.17it/s]
# 100%|██████████████████████████████████| 8714/8714 [00:00<00:00, 1434988.81it/s]
# 100%|█████████████████████████████████| 69708/69708 [00:00<00:00, 534532.67it/s]
# 100%|███████████████████████████████████| 8714/8714 [00:00<00:00, 482198.04it/s]
# 100%|███████████████████████████████████| 8714/8714 [00:00<00:00, 478285.79it/s]
# 100%|████████████████████████████████| 69708/69708 [00:00<00:00, 1028690.75it/s]
# 100%|███████████████████████████████████| 8714/8714 [00:00<00:00, 958264.47it/s]
# 100%|███████████████████████████████████| 8714/8714 [00:00<00:00, 964586.97it/s]
# dataset java read ! done !
#
# src_train set: 69708
# src_dev set: 8714
# src_test set: 8714
# tgt_train set: 69708
# tgt_dev set: 8714
# tgt_test set: 8714
# Done
# ************************************************************
# totally 9149 cases
# totally 7549 cases
# totally 9147 cases
# totally 9015 cases
# OK
#
# Process finished with exit code 0

# ************************************************************
# totally 21856 cases
# totally 21963 cases
# totally 20489 cases
# totally 20648 cases
# ************************************************************
# totally 20061 cases
# totally 19791 cases
# totally 20684 cases
# totally 19923 cases