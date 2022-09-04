
import numpy as np
from soupsieve import select
from utils_ahead import python_tokenize
from tree_sitter import Language, Parser
from utils import remove_comments_and_docstrings, tree_to_token_index, index_to_code_token, tree_to_variable_index, tree_to_token_index_pro
import itertools
import networkx as nx
import datetime
import os

from collections import Counter

text = 'hello world hello world hello hello world hello world'

print(Counter(text.split()))


def get_info_if(src, tgt):
    assert len(src) == len(tgt)
    selected_idx = []
    if_in_src = []
    if_in_tgt = []
    summary_text_all = ""
    for i in range(len(src)):
        src_item = src[i]
        tgt_item = tgt[i]
        # ① source code 中有 if statement，而且summary 中也有 or 或 if 的自然语言
        # 那么我们就认为 这是一个 代码结构信息在 自然语言中的体现
        if ('if' in src_item and ' or ' in tgt_item) or ('if' in src_item and ' if ' in tgt_item):
            selected_idx.append(i)
            summary_text_all += tgt_item
            summary_text_all += '\n'
        # ② 源代码中有 if statement
        if ('if' in src_item):
            if_in_src.append(i)
            # summary_text_all += tgt_item
            # summary_text_all += '\n'
        # ③ summary 中有 if 或 or 的自然语言
        if (' or ' in tgt_item) or (' if ' in tgt_item):
            if_in_tgt.append(i)

    print("【if】 Both in src and tgt :", len(selected_idx))
    print("【if】 in src :", len(if_in_src))
    print("【if or】 in tgt :", len(if_in_tgt))

    print(len(selected_idx), len(src))
    return selected_idx, if_in_src, if_in_tgt, summary_text_all



def get_info_for_while(src, tgt):
    assert len(src) == len(tgt)
    selected_idx = []
    for_while_in_src = []
    # if_in_tgt = []
    summary_text_all = ""
    for i in range(len(src)):
        src_item = src[i]
        tgt_item = tgt[i]
        # ① source code 中有 if statement，而且summary 中也有 or 或 if 的自然语言
        # 那么我们就认为 这是一个 代码结构信息在 自然语言中的体现
        if (('for_statement' in src_item or 'while_statement' in src_item or 'for_in_clause' in src_item) and (' from ' in tgt_item)) or\
                (('for_statement' in src_item or 'while_statement' in src_item or 'for_in_clause' in src_item) and (' in ' in tgt_item)):

            summary_text_all += tgt_item
            summary_text_all += '\n'
            for_while_in_src.append(i)
        # if 'for' in src_item:
        #     print(src_item)
    print("【for or while】 in src :", len(for_while_in_src))
    # print("【if or】 in tgt :", len(if_in_tgt))

    print(len(for_while_in_src), len(src))
    return for_while_in_src, summary_text_all


def read_from_raw():
    from utils_ahead import read_source_files, read_src_and_tgt_files, read_frm_sgtrans
    # 55538 18505 18502 train devv test
    # src_raw_train, src_raw_dev, src_raw_test = read_source_files()
    # src_raw_train, src_raw_dev, src_raw_test, tgt_raw_train, tgt_raw_dev, tgt_raw_test, test_guid = read_src_and_tgt_files()
    sources_raw_test, targets_raw_test, test_guid = read_src_and_tgt_files()

    dataset = {
        # 'train': src_raw_train,
        # 'dev': src_raw_dev,
        'test': sources_raw_test,
        # 'tgt_train':tgt_raw_train,
        # 'tgt_dev':tgt_raw_dev,
        'tgt_test':targets_raw_test,
        'test_guid':test_guid
    }

    return dataset


def save_v3():

    dataset = read_from_raw()
    # keys   'train', 'dev', 'test', 'tgt_train', 'tgt_dev', 'tgt_test', 'test_guid'
    src_test = dataset['test']
    guid_test = dataset['test_guid']
    tgt_test = dataset['tgt_test']
    assert len(src_test)==len(guid_test)==len(tgt_test)


    #====================
    from utils_ahead import read_frm_sgtrans,read_frm_ahead
    src_test, src_train,src_dev, tgt_test,tgt_train, tgt_dev, intok_test, instm_test, source_dataflow_sp = read_frm_ahead()
    for_while_in_src, summary_text_all = get_info_for_while(src_test, tgt_test)

    selected = [guid_test[idx] for idx in for_while_in_src]
    selected_sum = [tgt_test[idx] for idx in for_while_in_src]
    # selected_idx, selected_guid = from_raw_split_if_and_or(dataset['test'], dataset['tgt_test'], dataset['test_guid'])

    selected_idx = for_while_in_src
    selected_guid = selected
    # selected_idx, selected_guid = from_raw_split_if_and_or(dataset['test'], dataset['tgt_test'], dataset['test_guid'])
    assert len(selected_idx) == len(selected_guid)
    # print("OK")


    file_dir = './python_loop_20230901/'
    if not os.path.exists(file_dir):
        os.makedirs(file_dir)
    src_string, tgt_string, guid = [], [], []
    with open(file_dir + 'test.token.code', 'w', encoding='utf8') as f:
        with open(file_dir + 'test.token.guid', 'w', encoding='utf8') as g:
            with open(file_dir + 'test.token.nl', 'w', encoding='utf8') as h:

                for idx, idx_in_ori in enumerate(selected_idx):
                    sguid_1 = selected_guid[idx]
                    sguid_2 = guid_test[idx_in_ori]
                    assert sguid_1 == sguid_2
                    # print(sguid_1, sguid_2)
                    src_raw = src_test[idx_in_ori]
                    tgt_raw = tgt_test[idx_in_ori]

                    src_string.append(src_raw + '\n')
                    tgt_string.append(tgt_raw + '\n')
                    guid.append(str(sguid_2) + '\n')
                assert len(src_string)==len(tgt_string)==len(guid)
                f.writelines(src_string)
                g.writelines(guid)
                h.writelines(tgt_string)
                # t.append(datetime.datetime.now())

    print("Done")

    return 0

def save_sgtrans_v3():
    from utils_ahead import read_frm_sgtrans,read_frm_ahead, read_source_files

    src_test, src_train,src_dev, tgt_test,tgt_train, tgt_dev, intok_test, instm_test, source_dataflow_sp = read_frm_ahead()

    for_while_in_src, summary_text_all = get_info_for_while(src_test, tgt_test)

#========================
    src_test, _, _, _, _ = read_frm_sgtrans()
    # keys   'train', 'dev', 'test', 'tgt_train', 'tgt_dev', 'tgt_test', 'test_guid'



    file_dir = './sgtrans/'
    if not os.path.exists(file_dir):
        os.makedirs(file_dir)
    np.save(file_dir + 'dataflow_subtoken_v3.npy', source_dataflow_sp[for_while_in_src])
    # src_string, tgt_string, intok_string, instm_string, guid = [], [], [], [], []
    src_string, tgt_string, intok_string, instm_string= [], [], [], []
    with open(file_dir + 'code.original_subtoken', 'w', encoding='utf8') as f:
        with open(file_dir + 'code.intoken', 'w', encoding='utf8') as g:
            with open(file_dir + 'code.instatement', 'w', encoding='utf8') as h:
                with open(file_dir + 'javadoc.original', 'w', encoding='utf8') as j:
                    for idx_in_ori in for_while_in_src:

                        # print(sguid_1, sguid_2)
                        src_raw = src_test[idx_in_ori]
                        tgt_raw = tgt_test[idx_in_ori]
                        intok = intok_test[idx_in_ori]
                        instm = instm_test[idx_in_ori]

                        # print(src_raw)
                        # print(tgt_raw)
                        # print(intok)
                        # print(instm)
                        # print("====" * 10)
                        src_string.append(src_raw + '\n')
                        tgt_string.append(tgt_raw + '\n')
                        intok_string.append(intok + '\n')
                        instm_string.append(instm + '\n')
                        # guid.append(str(idx_in_ori))
                    # assert len(src_string)==len(tgt_string)==len(guid)
                    f.writelines(src_string)
                    g.writelines(intok_string)
                    h.writelines(instm_string)
                    j.writelines(tgt_string)
                # t.append(datetime.datetime.now())
    print("Done")



if __name__ == '__main__':
    # code = """
    #
    # def sample():
    #     a = random()
    #     if a % 2 == 0:
    #         b = a + 1
    #         print(b)
    #
    # """
    save_v3()
    save_sgtrans_v3()

    print("OK")


