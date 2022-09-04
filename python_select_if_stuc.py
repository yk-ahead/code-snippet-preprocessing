
import numpy as np
from soupsieve import select
from utils_ahead import python_tokenize
from tree_sitter import Language, Parser
from utils import remove_comments_and_docstrings, tree_to_token_index, index_to_code_token, tree_to_variable_index, tree_to_token_index_pro
import itertools
import networkx as nx
import datetime
import os



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




def from_raw_split_if_and_or(src, tgt, guid=None):
    # assert len(src) == len(tgt) == len(guid)
    selected_idx, selected_guid = [], []
    for i in range(len(src)):
        src_item = src[i]
        tgt_item = tgt[i]
        if guid:
            guid_item = guid[i]
        #
        if (' if ' in src_item and ' or ' in tgt_item) or (' if ' in src_item and ' if ' in tgt_item):

            selected_idx.append(i)
            if guid:
                selected_guid.append(guid_item)

    print(len(selected_idx), len(src))
    return selected_idx, selected_guid

def save_v2():

    dataset = read_from_raw()
    # keys   'train', 'dev', 'test', 'tgt_train', 'tgt_dev', 'tgt_test', 'test_guid'
    src_test = dataset['test']
    guid_test = dataset['test_guid']
    tgt_test = dataset['tgt_test']
    assert len(src_test)==len(guid_test)==len(tgt_test)

    selected_idx, selected_guid = from_raw_split_if_and_or(dataset['test'], dataset['tgt_test'], dataset['test_guid'])
    assert len(selected_idx) == len(selected_guid)
    # print("OK")

    file_dir = './python_if_20230901/'
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




if __name__ == '__main__':
    code = """
    
    def sample():
        a = random()
        if a % 2 == 0:
            b = a + 1
            print(b)
            
    """
    save_v2()
    print("OK")
