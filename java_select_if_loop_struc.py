import os
import re
import datetime
import numpy as np
from tqdm import tqdm
import subprocess
import itertools
import networkx as nx
# from DFG import DFG_java
from tree_sitter import Language, Parser
from utils import remove_comments_and_docstrings,\
    tree_to_token_index, tree_to_token_index_pro\
    , index_to_code_token, tree_to_variable_index

def DFG_java(root_node, index_to_code, states):
    assignment = ['assignment_expression']
    def_statement = ['variable_declarator']
    increment_statement = ['update_expression']
    if_statement = ['if_statement', 'else']
    for_statement = ['for_statement']
    enhanced_for_statement = ['enhanced_for_statement']
    while_statement = ['while_statement']
    do_first_statement = []
    states = states.copy()
    if (len(root_node.children) == 0 or root_node.type == 'string') and root_node.type != 'comment':
        idx, code = index_to_code[(root_node.start_point, root_node.end_point)]
        if root_node.type == code:
            return [], states
        elif code in states:
            return [(code, idx, 'comesFrom', [code], states[code].copy())], states
        else:
            if root_node.type == 'identifier':
                states[code] = [idx]
            return [(code, idx, 'comesFrom', [], [])], states
    elif root_node.type in def_statement:
        name = root_node.child_by_field_name('name')
        value = root_node.child_by_field_name('value')
        DFG = []
        if value is None:
            indexs = tree_to_variable_index(name, index_to_code)
            for index in indexs:
                idx, code = index_to_code[index]
                DFG.append((code, idx, 'comesFrom', [], []))
                states[code] = [idx]
            return sorted(DFG, key=lambda x: x[1]), states
        else:
            name_indexs = tree_to_variable_index(name, index_to_code)
            value_indexs = tree_to_variable_index(value, index_to_code)
            temp, states = DFG_java(value, index_to_code, states)
            DFG += temp
            for index1 in name_indexs:
                idx1, code1 = index_to_code[index1]
                for index2 in value_indexs:
                    idx2, code2 = index_to_code[index2]
                    DFG.append((code1, idx1, 'comesFrom', [code2], [idx2]))
                states[code1] = [idx1]
            return sorted(DFG, key=lambda x: x[1]), states
    elif root_node.type in assignment:
        left_nodes = root_node.child_by_field_name('left')
        right_nodes = root_node.child_by_field_name('right')
        DFG = []
        temp, states = DFG_java(right_nodes, index_to_code, states)
        DFG += temp
        name_indexs = tree_to_variable_index(left_nodes, index_to_code)
        value_indexs = tree_to_variable_index(right_nodes, index_to_code)
        for index1 in name_indexs:
            idx1, code1 = index_to_code[index1]
            for index2 in value_indexs:
                idx2, code2 = index_to_code[index2]
                DFG.append((code1, idx1, 'computedFrom', [code2], [idx2]))
            states[code1] = [idx1]
        return sorted(DFG, key=lambda x: x[1]), states
    elif root_node.type in increment_statement:
        DFG = []
        indexs = tree_to_variable_index(root_node, index_to_code)
        for index1 in indexs:
            idx1, code1 = index_to_code[index1]
            for index2 in indexs:
                idx2, code2 = index_to_code[index2]
                DFG.append((code1, idx1, 'computedFrom', [code2], [idx2]))
            states[code1] = [idx1]
        return sorted(DFG, key=lambda x: x[1]), states
    elif root_node.type in if_statement:
        DFG = []
        current_states = states.copy()
        others_states = []
        flag = False
        tag = False
        if 'else' in root_node.type:
            tag = True
        for child in root_node.children:
            if 'else' in child.type:
                tag = True
            if child.type not in if_statement and flag is False:
                temp, current_states = DFG_java(child, index_to_code, current_states)
                DFG += temp
            else:
                flag = True
                temp, new_states = DFG_java(child, index_to_code, states)
                DFG += temp
                others_states.append(new_states)
        others_states.append(current_states)
        if tag is False:
            others_states.append(states)
        new_states = {}
        for dic in others_states:
            for key in dic:
                if key not in new_states:
                    new_states[key] = dic[key].copy()
                else:
                    new_states[key] += dic[key]
        for key in new_states:
            new_states[key] = sorted(list(set(new_states[key])))
        return sorted(DFG, key=lambda x: x[1]), new_states
    elif root_node.type in for_statement:
        DFG = []
        for child in root_node.children:
            temp, states = DFG_java(child, index_to_code, states)
            DFG += temp
        flag = False
        for child in root_node.children:
            if flag:
                temp, states = DFG_java(child, index_to_code, states)
                DFG += temp
            elif child.type == "local_variable_declaration":
                flag = True
        dic = {}
        for x in DFG:
            if (x[0], x[1], x[2]) not in dic:
                dic[(x[0], x[1], x[2])] = [x[3], x[4]]
            else:
                dic[(x[0], x[1], x[2])][0] = list(set(dic[(x[0], x[1], x[2])][0] + x[3]))
                dic[(x[0], x[1], x[2])][1] = sorted(list(set(dic[(x[0], x[1], x[2])][1] + x[4])))
        DFG = [(x[0], x[1], x[2], y[0], y[1]) for x, y in sorted(dic.items(), key=lambda t: t[0][1])]
        return sorted(DFG, key=lambda x: x[1]), states
    elif root_node.type in enhanced_for_statement:
        name = root_node.child_by_field_name('name')
        value = root_node.child_by_field_name('value')
        body = root_node.child_by_field_name('body')
        DFG = []
        for i in range(2):
            temp, states = DFG_java(value, index_to_code, states)
            DFG += temp
            name_indexs = tree_to_variable_index(name, index_to_code)
            value_indexs = tree_to_variable_index(value, index_to_code)
            for index1 in name_indexs:
                idx1, code1 = index_to_code[index1]
                for index2 in value_indexs:
                    idx2, code2 = index_to_code[index2]
                    DFG.append((code1, idx1, 'computedFrom', [code2], [idx2]))
                states[code1] = [idx1]
            temp, states = DFG_java(body, index_to_code, states)
            DFG += temp
        dic = {}
        for x in DFG:
            if (x[0], x[1], x[2]) not in dic:
                dic[(x[0], x[1], x[2])] = [x[3], x[4]]
            else:
                dic[(x[0], x[1], x[2])][0] = list(set(dic[(x[0], x[1], x[2])][0] + x[3]))
                dic[(x[0], x[1], x[2])][1] = sorted(list(set(dic[(x[0], x[1], x[2])][1] + x[4])))
        DFG = [(x[0], x[1], x[2], y[0], y[1]) for x, y in sorted(dic.items(), key=lambda t: t[0][1])]
        return sorted(DFG, key=lambda x: x[1]), states
    elif root_node.type in while_statement:
        DFG = []
        for i in range(2):
            for child in root_node.children:
                temp, states = DFG_java(child, index_to_code, states)
                DFG += temp
        dic = {}
        for x in DFG:
            if (x[0], x[1], x[2]) not in dic:
                dic[(x[0], x[1], x[2])] = [x[3], x[4]]
            else:
                dic[(x[0], x[1], x[2])][0] = list(set(dic[(x[0], x[1], x[2])][0] + x[3]))
                dic[(x[0], x[1], x[2])][1] = sorted(list(set(dic[(x[0], x[1], x[2])][1] + x[4])))
        DFG = [(x[0], x[1], x[2], y[0], y[1]) for x, y in sorted(dic.items(), key=lambda t: t[0][1])]
        return sorted(DFG, key=lambda x: x[1]), states
    else:
        DFG = []
        for child in root_node.children:
            if child.type in do_first_statement:
                temp, states = DFG_java(child, index_to_code, states)
                DFG += temp
        for child in root_node.children:
            if child.type not in do_first_statement:
                temp, states = DFG_java(child, index_to_code, states)
                DFG += temp

        return sorted(DFG, key=lambda x: x[1]), states


dfg_function={
    # 'python':DFG_python,
    'java':DFG_java,
    # 'ruby':DFG_ruby,
    # 'go':DFG_go,
    # 'php':DFG_php,
    # 'javascript':DFG_javascript
}

parsers={}
for lang in dfg_function:
    LANGUAGE = Language('build/yk-languages.so', lang)
    parser = Parser()
    parser.set_language(LANGUAGE)
    parser = [parser,dfg_function[lang]]
    parsers[lang]= parser



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


def python_tokenize(line):

    tokens = re.split('\.|\(|\)|\:| |;|,|!|=|[|]|', line)

    tokens = [t for t in tokens if t]
    temp = []
    for item in tokens:
        splt = split_identifier_into_parts(item)
        temp += splt
    return temp

def count_file_lines(file_path):
    """
    Counts the number of lines in a file using wc utility.
    :param file_path: path to file
    :return: int, no of lines
    """
    num = subprocess.check_output(['wc', '-l', file_path])
    num = num.decode('utf-8').split(' ')
    return int(num[0])

def read_source_files(lang = 'java'):
    "/home/yangkang/container_data/Pooling/Parser/PYTHON/"
    # "/home/yangkang/container_data/Pooling/Parser/JAVA/"
    if lang == "python":
        _dir_ = '../DATA_RAW/PYTHON/'
    else:
        _dir_ = '../DATA_RAW/JAVA/'
    filenames = {
        'src_raw_train': _dir_ + 'train/code.original',
        'src_raw_dev':   _dir_ + 'dev/code.original',
        'src_raw_test':  _dir_ + 'test/code.original',
        'tgt_raw_train': _dir_ + 'train/javadoc.original',
        'tgt_raw_dev':   _dir_ + 'dev/javadoc.original',
        'tgt_raw_test':  _dir_ + 'test/javadoc.original',
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


    with open(filenames['tgt_raw_train']) as f:
        targets_raw_train = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['tgt_raw_train']))]
    with open(filenames['tgt_raw_dev']) as f:
        targets_raw_dev = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['tgt_raw_dev']))]
    with open(filenames['tgt_raw_test']) as f:
        targets_raw_test = [line.strip() for line in
                      tqdm(f, total=count_file_lines(filenames['tgt_raw_test']))]


    print("dataset {} read ! done !\n".format(lang))

    dataset = {
        'src_train': sources_raw_train,
        'src_dev': sources_raw_dev,
        'src_test': sources_raw_test,
        'tgt_train':targets_raw_train,
        'tgt_dev':targets_raw_dev,
        'tgt_test':targets_raw_test
    }
    for key in dataset.keys():
        print("{} set: {}".format(key, len(dataset[key])))

    assert len(dataset['src_train']) == len(dataset['tgt_train'])
    assert len(dataset['src_dev']) == len(dataset['tgt_dev'])
    assert len(dataset['src_test']) == len(dataset['tgt_test'])

    return dataset
    # return  sources_raw_train, sources_raw_dev, sources_raw_test,

def get_info_if(src, tgt):
    assert len(src) == len(tgt)
    selected_idx = []
    if_in_src = []
    if_in_tgt = []
    summary_text_all = ""
    summary_text = ""
    for i in range(len(src)):
        src_item = src[i]
        tgt_item = tgt[i]
        # ① source code 中有 if statement，而且summary 中也有 or 或 if 的自然语言
        # 那么我们就认为 这是一个 代码结构信息在 自然语言中的体现
        if (' if ' in src_item and ' or ' in tgt_item) or (' if ' in src_item and ' if ' in tgt_item):
            selected_idx.append(i)
            summary_text_all += tgt_item
            summary_text_all += '\n'
        # ② 源代码中有 if statement
        if (' if ' in src_item):
            if_in_src.append(i)
            summary_text += tgt_item
            summary_text += '\n'
        # ③ summary 中有 if 或 or 的自然语言
        if (' or ' in tgt_item) or (' if ' in tgt_item):
            if_in_tgt.append(i)

    # print("【if】 Both in src and tgt :", len(selected_idx))
    print("【if】 in src :", len(if_in_src))
    print("【if/or】 in tgt :", len(if_in_tgt))

    print("【if】 in src and 【or/if】 in tgt:", len(selected_idx))
    print("【All】 cases",len(src))
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
        if (' for ' in src_item or ' while ' in src_item):
        # if ('for_statement' in src_item or 'while_statement' in src_item or 'for_in_clause' in src_item) and (' from ' in tgt_item):
        # if ('for_statement' in src_item or 'while_statement' in src_item) and (' from ' in tgt_item):
        # if ('for_statement' in src_item or 'while_statement' in src_item) and ((' in ' in tgt_item) or (' from ' in tgt_item)):
            # selected_idx.append(i)
            # summary_text_all += tgt_item
            # summary_text_all += '\n'
            for_while_in_src.append(i)
        if ((' for ' in src_item or ' while ' in src_item) and ' in ' in tgt_item) or\
            ((' for ' in src_item or ' while ' in src_item) and ' from ' in tgt_item):
        # if ((' for ' in src_item or ' while ' in src_item) and 'from ' in tgt_item):
            selected_idx.append((i))
            summary_text_all += tgt_item
            summary_text_all += '\n'
        # if 'for' in src_item:
        #     print(src_item)
    print("【for or while】 in src :", len(for_while_in_src))
    # print("【if or】 in tgt :", len(if_in_tgt))

    print(len(for_while_in_src), len(src))
    print("【for/while】 in src and 【in/from】 in tgt:", len(selected_idx))
    return selected_idx, summary_text_all


def save_struc_stm_java():
    dfg_function = {
        # 'python': DFG_python,
        'java':DFG_java,
        # 'ruby':DFG_ruby,
        # 'go':DFG_go,
        # 'php':DFG_php,
        # 'javascript':DFG_javascript
    }

    parsers = {}
    for lang in dfg_function:
        LANGUAGE = Language('build/yk-languages.so', lang)
        parser = Parser()
        parser.set_language(LANGUAGE)
        parser = [parser, dfg_function[lang]]
        parsers[lang] = parser

    print("OK")
    print("parser Ready !")
    print(datetime.datetime.now())

    dataset = read_source_files()

    # src_train = dataset['src_train']
    # src_dev = dataset['src_dev']
    src_test = dataset['src_test']

    # tgt_train = dataset['tgt_train']
    # tgt_dev = dataset['tgt_dev']
    tgt_test = dataset['tgt_test']

    print(datetime.datetime.now())

    selected_idx_if, if_in_src, if_in_tgt, summary_text_all = get_info_if(src_test, tgt_test)
    selected_idx_loop, summary_text_all = get_info_for_while(src_test, tgt_test)

    V5_dir = "../DATA_RAW/java_0725/java/"
    with open(V5_dir + "test.token.guid") as f:
        V5_test_guid = [line.strip() for line in
                   tqdm(f, total=count_file_lines(V5_dir + "test.token.guid"))]

    with open(V5_dir + "test.token.code") as f:
        V5_test_code = [line.strip() for line in
                   tqdm(f, total=count_file_lines(V5_dir + "test.token.code"))]

    with open(V5_dir + "test.token.nl") as f:
        V5_test_nl = [line.strip() for line in
                   tqdm(f, total=count_file_lines(V5_dir + "test.token.nl"))]

    # 从 处理好的数据集中选取 test guid 为 selected 的那部分
    selected_if_guid = [V5_test_guid[idx] for idx in selected_idx_if]
    selected_loop_guid = [V5_test_guid[idx] for idx in selected_idx_loop]

    # selected = selected_idx_if
    # file_dir = './java_if_20230901/'

    selected = selected_idx_loop
    file_dir = './java_loop_20230901/'

    if not os.path.exists(file_dir):
        os.makedirs(file_dir)
    src_string, tgt_string, guid = [], [], []
    with open(file_dir + 'test.token.code', 'w', encoding='utf8') as f:
        with open(file_dir + 'test.token.guid', 'w', encoding='utf8') as g:
            with open(file_dir + 'test.token.nl', 'w', encoding='utf8') as h:

                for idx, idx_in_ori in enumerate(selected):
                    # if
                    # sguid_1 = selected_if_guid[idx]
                    # sguid_2 = V5_test_guid[idx_in_ori]

                    # # loop
                    sguid_1 = selected_loop_guid[idx]
                    sguid_2 = V5_test_guid[idx_in_ori]

                    assert sguid_1 == sguid_2
                    # print(sguid_1, sguid_2)
                    src_raw = V5_test_code[idx_in_ori]
                    tgt_raw = V5_test_nl[idx_in_ori]

                    src_string.append(src_raw + '\n')
                    tgt_string.append(tgt_raw + '\n')
                    guid.append(str(sguid_2) + '\n')
                assert len(src_string)==len(tgt_string)==len(guid)
                f.writelines(src_string)
                g.writelines(guid)
                h.writelines(tgt_string)
                # t.append(datetime.datetime.now())

    print("Done")


if __name__ == '__main__':
    # save_matrix_npy_java()
    save_struc_stm_java()
    print("OK")
