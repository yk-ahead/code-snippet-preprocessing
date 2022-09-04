import re
import os
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

def read_source_files():
    _dir_ = '../DATA_RAW/JAVA/'
    filenames = {
        'src_raw_train': _dir_ + 'train/code.original',
        'src_raw_dev': _dir_ + 'dev/code.original',
        'src_raw_test': _dir_ + 'test/code.original',
        'tgt_raw_train': _dir_ + 'train/javadoc.original',
        'tgt_raw_dev': _dir_ + 'dev/javadoc.original',
        'tgt_raw_test': _dir_ + 'test/javadoc.original',
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


    print("dataset read ! done !\n")

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



def read_from_raw():
    # 55538 18505 18502 train devv test
    # ['train', 'dev', 'test']
    src_raw_train, src_raw_dev, src_raw_test = read_source_files()
    dataset = {
        'train': src_raw_train,
        'dev': src_raw_dev,
        'test': src_raw_test,
    }
    for key in dataset.keys():
        print("{} set: {}".format(key, len(dataset[key])))
    return dataset


def walk(tree):
    '''
    遍历 AST ， 中序遍历满，符合代码 token 在原始code snippet 中的顺序
    :param tree: tree_sitter.Tree Object
    :return: list of AST nodes
    '''
    # tree = parser[0].parse(bytes(code, 'utf8'))
    ast = []
    root = tree.root_node
    stack = [root]
    while stack:
        current = stack.pop()
        children = []
        ins = len(stack)
        for c in current.children:
            children += [c]
            stack.insert(ins, c)
        # ast += [{"current": current, "children": children}]
        ast.append(current)
    return ast

def get_adj_from_ast(tree, all_nodes = None):
    '''
    从 AST 中 得到以此 为 无向图的邻接矩阵 adjacency matrix
    :param tree: tree_sitter.Tree Object
    :param all_nodes: AST的所有节点
    :return:
    matrix AST adjacency matrix

    code_snippet_tokens 按照代码原始顺序的AST node tokens （包括AST的中间节点）  ['module', 'function_definition', 'def',
    'identifier', 'parameters', '(', ')', ':', 'block', 'expression_statement', 'assignment', 'identifier', '=',
    'call', 'identifier', 'argument_list', '(', ')', 'if_statement', 'if', 'comparison_operator', 'binary_operator',
    'identifier', '%', 'integer', '==', 'integer', ':', 'block', 'expression_statement', 'assignment', 'identifier',
    '=', 'binary_operator', 'identifier', '+', 'integer', 'expression_statement', 'call', 'identifier',
    'argument_list', '(', 'identifier', ')']

    ast   node type child_idxs
        [{
            'current': node,
            'current_type':node.type,
            'children_index':[all_nodes.index(child) for child in node.children]
        }, {}, ... ,{}]
    '''
    if all_nodes==None:
        all_nodes = walk(tree)
    ast = []
    code_snippet_tokens = []
    for node in all_nodes:
        ast.append({
            'current': node,
            'current_type':node.type,
            # 'is_named':node.is_named,
            # 'children':node.children,
            'children_index':[all_nodes.index(child) for child in node.children]
        })

        code_snippet_tokens.append(node.type)

    length = len(ast)
    matrix = np.zeros([length, length], dtype=np.bool) if length <= 512 else np.zeros([length, length], dtype=np.bool)

    for i, node in enumerate(ast):
        matrix[i][i] = 1
        for j in node['children_index']:
            matrix[i][j] = 1
            matrix[j][i] = 1

    return matrix, code_snippet_tokens, ast, all_nodes



def extract_dataflow(code, parser, lang):
    '''
    利用DFG.py 文件中的， DFG_python(), 从 code 中得到 数据流，变量之间的数据流动
    即，
    :param code:
    :param parser:
    :param lang:
    :return:
    code_tokens  只包含叶子节点，原始的代码 tokens  ['def', 'sample', '(', ')', ':', 'a', '=', 'random', '(', ')', 'if',
                    'a', '%', '2', '==', '0', ':', 'b', '=', 'a', '+', '1', 'print', '(', 'b', ')']
    dfg
    [('a', 5, 'computedFrom', ['random'], [7]),
    ('a', 11, 'comesFrom', ['a'], [5]),
    ('b', 17, 'computedFrom', ['a', '1'], [19, 21]),

    code_snippet_tokens   叶子节点以及 中间节点

    '''
    # try:
    #     code=remove_comments_and_docstrings(code,lang)
    # except:
    #     pass

    #obtain dataflow
    if lang=="php":
        code="<?php"+code+"?>"
    try:
        tree = parser[0].parse(bytes(code,'utf8'))
        root_node = tree.root_node
        # tokens_index=tree_to_token_index(root_node)
        mapping_nodes, tokens_index=tree_to_token_index_pro(root_node)
        code=code.split('\n')
        code_tokens=[index_to_code_token(x,code) for x in tokens_index]
        index_to_code={}
        for idx,(index,code) in enumerate(zip(tokens_index,code_tokens)):
            index_to_code[index]=(idx,code)
        try:
            DFG,_=parser[1](root_node,index_to_code,{})
        except:
            DFG=[]
        DFG=sorted(DFG,key=lambda x:x[1])
        indexs=set()
        for d in DFG:
            if len(d[-1])!=0:
                indexs.add(d[1])
            for x in d[-1]:
                indexs.add(x)
        new_DFG=[]
        for d in DFG:
            if d[1] in indexs:
                new_DFG.append(d)
        dfg=new_DFG
    except:
        dfg=[]
    adj, code_snippet_tokens, ast_nodes, all_nodes = get_adj_from_ast(tree)
    return code_tokens,dfg,code_snippet_tokens, adj, mapping_nodes, ast_nodes, all_nodes, tree
    # return dfg


def asts2tokens_nodes(tree):
    '''

    :param tree:
    :return:
    all_nodes_tokens :   自定义的字典 list，包含了所有的 AST nodes 以及相关的两个属性，leaf node.text, non-leaf node.type
    [
    {'current_ast_node': Node,
     'node_token': 'assignment',
     'children': [ < Node ,Node, ... ,Node >]},  {}, ..., {}
    ],
    all_tokens : 字符串list，去掉了 空字符串的 leaf node.text, non-leaf node.type, 【作为最终的输入文本】
    mapping_tgt_tks_to_ast_nodes, mapping_ast_nodes_to_tgt_tks
    '''
    def get_token(node, lower = False):
        """
        Get the token of an ast node,
        the token of a leaf node is its text in code,
        the token of a non-leaf node is its ast type.
        """
        if not node.is_named:
            token = ""
        else:
            if len(node.children) == 0:
                token = re.sub(r"\s", "", str(node.text, "utf-8"))
            else:
                token = node.type
        if lower:
            return token.lower()
        return token, node

    def get_child(node):
        """Get all children of an ast node.
        """
        return node.children

    def get_sequence(node, sequence, all_nodes_tokens):
        token, c_node = get_token(node)
        children = get_child(node)
        all_nodes_tokens.append(
            {
                'current_ast_node': node,
                'node_token':token,
                'children': children
            }
        )
        if token != "":
            sequence.append(token)
        for child in children:
            get_sequence(child, sequence, all_nodes_tokens)

    def token_statistic(all_tokens):
        count = dict()
        for token in all_tokens:
            try:
                count[token] += 1
            except Exception:
                count[token] = 1
        return count

    all_nodes_tokens = []
    all_tokens = []
    get_sequence(tree.root_node, all_tokens, all_nodes_tokens)

    mapping_tgt_tks_to_ast_nodes = {}
    mapping_ast_nodes_to_tgt_tks = {}
    all_tokens_temp = []
    for idx, item in enumerate(all_nodes_tokens):
        if item['node_token']:
            f_idx = len(all_tokens_temp)
            all_tokens_temp.append(item['node_token'])
            mapping_tgt_tks_to_ast_nodes[f_idx] = idx
            mapping_ast_nodes_to_tgt_tks[idx] = f_idx
        else:
            mapping_ast_nodes_to_tgt_tks[idx] = -1

    assert all_tokens == all_tokens_temp

    return all_nodes_tokens, all_tokens, mapping_tgt_tks_to_ast_nodes, mapping_ast_nodes_to_tgt_tks



def add_dfg_to_adj(code_tokens, dfg, code_snippet_tokens, mapping_nodes, ast_nodes):
    '''

    :param code_tokens: 原始的 code snippet 的tokens，全是叶子 没有中间节点
    :param dfg: 通过DFG.py 得到的DFG 的边，节点与 code_tokens 相同
    :param code_snippet_tokens: 包含所有的ast 中的中间节点以及叶子节点的node.type（字符串） 的list
    :param adj: 节点为ast 中所有的 中间以及叶子节点的 邻接矩阵，asj的节点与code_snippet_tokens 相同
    :param mapping_nodes: 叶子节点到 所有节点 的映射 ，叶子节点 到 ast全部节点中的 index 映射
    :param ast_nodes: [ {
    'current': <Node kind=module, start_point=(0, 0), end_point=(5, 16)>,
    'current_type': 'module',
    'children_index': [1]
    } , ..., ]
    :return: df_edges_in_dfg, df_edges_in_ast, 数据流的边，在叶子节点之间的index二元组，以及在 全部ast节点中的index二元组
    '''
    assert len(code_tokens) == len(mapping_nodes)
    assert len(code_snippet_tokens) == len(ast_nodes)
    ast_nodes = [node['current'] for node in ast_nodes]
    dfgINast_index = []
    for dfg_node in mapping_nodes:
        dfgINast_index.append(ast_nodes.index(dfg_node))
    mapping = dict(zip(range(len(code_tokens)), dfgINast_index))


    df_edges_in_dfg = []
    df_edges_in_ast = []

    for edge in dfg:
        (src, src_index, edge_type, tgts_list, tgts_idx_list) = edge
        # print(src, src_index, edge_type, tgts_list, tgts_idx_list)
        if tgts_list == []:
            continue
        assert code_tokens[src_index] == src
        # assert len(tgts_list) == len(tgts_idx_list)
        # for i, t_idx in enumerate(tgts_idx_list):
        #     assert tgts_list[i] == code_tokens[t_idx]
        #     df_edges_in_dfg.append((src_index, t_idx))
        #     df_edges_in_ast.append((mapping[src_index], mapping[t_idx]))

        # 有这种情况 ('flashes', 75, 'comesFrom', ['flashes'], [13, 31])
        # 同一个变量，出现多次，在 tgts_list 中只出现一次
        if len(tgts_list) == len(tgts_idx_list):
            pass
        elif len(tgts_list) == 1:
            tgts_list = tgts_list * len(tgts_idx_list)
        else:
            # print(src, src_index, edge_type, tgts_list, tgts_idx_list)
            continue
        for i, t_idx in enumerate(tgts_idx_list):
            # assert tgts_list[i] == code_tokens[t_idx]
            df_edges_in_dfg.append((src_index, t_idx))
            df_edges_in_ast.append((mapping[src_index], mapping[t_idx]))
    return df_edges_in_dfg, df_edges_in_ast


def extract_statement(tree, all_nodes=None):
    '''
    从 AST 中 抽取 在同一个statement中的关系 边

    :param code:
    :param parser:
    :param lang:
    :return:
    '''
    # assignment = ['assignment', 'augmented_assignment', 'for_in_clause']
    # expression_statement = ['expression_statement']
    # if_statement = ['if_statement']
    # for_statement = ['for_statement']
    # while_statement = ['while_statement']
    # do_first_statement = ['for_in_clause']
    # def_statement = ['default_parameter']

    assignment = ['assignment_expression']
    def_statement = ['variable_declarator']
    increment_statement = ['update_expression']
    if_statement = ['if_statement', 'else']
    for_statement = ['for_statement']
    enhanced_for_statement = ['enhanced_for_statement']
    while_statement = ['while_statement']
    do_first_statement = []

    statements = assignment + if_statement + while_statement + for_statement + do_first_statement + def_statement\
    + enhanced_for_statement + increment_statement

    if all_nodes is None:
        all_nodes = walk(tree)


    all_edges = []
    def add_edges_betw_sub_tree_leaf(all_nodes, current_node):
        # edges = []
        # 判断 当前节点 的孩子节点有几个，如果 大于等于 2，就需要添加 边 ， 否则 返回空
        if len(current_node.children) > 1:
            children_idx = [all_nodes.index(child) for child in current_node.children]
            # edges.append(list(itertools.permutations(children_idx, 2)))
            edges.extend(list(itertools.combinations(children_idx, 2)))
        for child in current_node.children:
            add_edges_betw_sub_tree_leaf(all_nodes, child)
            # pass # 添加一些边

    # 遍历 目标 statement
    for node in all_nodes:
        if node.type in statements:
            edges = []
            add_edges_betw_sub_tree_leaf(all_nodes, node)
            all_edges.extend(edges)

    all_edges = list(set(all_edges))

    return all_edges


def combine_multi_view_matrix(adj_matrix, df_edges_in_dfg, df_edges_in_ast, statements_edges, code_tokens,
                              mapping_tgt_tks_to_ast_nodes, exact_flag=False):
    length = len(adj_matrix)
    dfg_matrix = np.zeros([length, length], dtype=np.bool)
    # matrix = np.zeros([512, 512], dtype=np.bool) if length <= 512 else np.zeros([length, length], dtype=np.bool)
    stm_matrix = np.zeros([length, length], dtype=np.bool)

    # for e in df_edges_in_dfg:
    #     print(code_tokens[e[0]], code_tokens[e[1]])
    for edge in df_edges_in_ast:
        # print(edge)
        s, t = edge
        # print(ast_nodes[s]['current'].type, ast_nodes[t]['current'].type)
        dfg_matrix[s][t] = 1
        # 注意 这里的dfg中的边，是有方向的
        # dfg_matrix[t][s] = 1
    for edge in statements_edges:
        s, t = edge
        stm_matrix[s][t] = 1
        stm_matrix[t][s] = 1
        # 注意 这里的 statement matrix 中的边，是没有方向的

    adj_dfg_stm = stm_matrix + dfg_matrix + adj_matrix
    # 筛选出某些行和列，这些 行/或者列 的index 为 挑选出来的将作为 输入文本的 token
    selected = list(mapping_tgt_tks_to_ast_nodes.values())
    # final_matrix = np.zeros([length, length], dtype=np.bool)
    final_matrix = adj_dfg_stm[selected][:, selected]
    # adj_dfg_stm = adj_dfg_stm[:512][:512]
    selected_adj = adj_matrix[selected][:, selected]
    selected_stm = stm_matrix[selected][:, selected]
    selected_dfg = dfg_matrix[selected][:, selected]

    # """
    # np.pad(final_matrix, ((3, 2), (2, 3)), 'constant')
    # ((1,1),(2,2))表示在二维数组array第一维（此处便是行）前面填充1行，最后面填充1行；
    #                  在二维数组array第二维（此处便是列）前面填充2列，最后面填充2列
    # constant_values=(0,3) 表示第一维填充0，第二维填充3
    # """
    # if exact_flag:
    #     # ！① 返回实际大小
    #     return final_matrix, selected_adj
    # else:
    #     # ！② 返回512大小
    #     assert  length > len(final_matrix)
    #     adj_dfg_stm = np.pad(final_matrix, ((0, length-len(final_matrix)), (0, length-len(final_matrix))), 'constant', constant_values=(0, 0))
    #     return adj_dfg_stm[:512][:512]
    return final_matrix, selected_adj, selected_stm, selected_dfg



def get_distance_matrix_from_ast(adj_matrix):
    leng = len(adj_matrix)
    G = nx.Graph(adj_matrix)
    lengths = dict(nx.all_pairs_shortest_path_length(G))  # 计算graph两两节点之间的最短路径的长度

    import numpy as np
    matrix = np.zeros([leng, leng], dtype=np.int)
    for i in lengths.keys():
        dist_dict = lengths[i]
        for j in dist_dict.keys():
            matrix[i][j] = dist_dict[j]
    # matrix = matrix[:512][:512]
    return matrix


def split_dfg_matrix_from_subtokens(selected_dfg, mul_view_matrix, code_tokens, all_tokens,
                                    mapping_tgt_tks_to_ast_nodes):
    # selected_adj, mul_view_matrix, code_tokens, all_tokens, mapping_tgt_tks_to_ast_nodes

    key_words = ['instanceof_expression', 'field_access', 'class', '...', 'assert', 'try_with_resources_statement', 'native',
 'labeled_statement', '%=', 'assignment_expression', 'default', '+', '>', 'return', 'inferred_parameters', '<<=',
 'super', 'identifier', '=', '/=', 'annotated_type', 'strictfp', 'yield', 'synchronized_statement', 'abstract',
 'annotation_argument_list', 'case', 'return_statement', '@', ';', 'binary_expression', 'enhanced_for_statement', '}',
 'program', 'dimensions', '>=', '^', ':', '^=', 'double', 'array_type', 'switch_expression', 'final', 'wildcard',
 'throws', 'else', 'scoped_type_identifier', 'object_creation_expression', 'synchronized', '||', '==', 'ERROR',
 'public', '.', 'block', '|', 'void_type', '*', 'switch', 'record', 'parenthesized_expression', 'throw_statement',
 'byte', '[', 'assert_statement', 'int', '++', '--', '!=', '>>=', '|=', 'try_statement', 'while', '+=', 'type_arguments',
 'break_statement', 'array_access', '%', 'class_declaration', 'field_declaration', 'break', '-', '{', 'array_initializer',
 'annotation', 'spread_parameter', 'expression_statement', 'formal_parameter', ',', 'boolean_type', 'cast_expression',
 'catch_type', 'do', 'static', 'marker_annotation', 'resource', 'class_literal', '<<', ']', '!', 'type_identifier',
 'continue_statement', 'float', '&', 'unary_expression', 'floating_point_type', 'finally', '~', 'catch_clause',
 'element_value_array_initializer', 'while_statement', 'do_statement', 'finally_clause', 'variable_declarator', '&&',
 'element_value_pair', 'modifiers', 'for', 'array_creation_expression', ')', 'method_invocation', 'if', 'integral_type',
 'argument_list', 'resource_specification', 'formal_parameters', 'class_body', 'switch_label', 'ternary_expression',
 'catch', 'char', 'catch_formal_parameter', 'switch_block', 'extends', 'private', 'this', '-=', 'try', 'scoped_identifier',
 'throw', '(', 'if_statement', 'update_expression', 'null_literal', '/', 'with', 'short', '?', 'generic_type', '&=',
 'long', 'continue', 'switch_block_statement_group', '<=', '*=', 'new', 'instanceof', 'dimensions_expr', '<', 'protected',
 'local_variable_declaration', 'for_statement', '>>>=']


    all_tokens_subtoks = []
    pos_tag = []
    pos = 0
    for i, t in enumerate(all_tokens):
        if t in key_words:
            toked = [t]
        else:
            toked = python_tokenize(t)
        pos_tag = [p for p in range(pos, pos + len(toked))]

        pos += len(toked)
        # print(i,  t, toked.__len__(),toked, pos_tag)
        # print()

        # if toked.__len__() > 1:
        all_tokens_subtoks.append(
            {
                "idxInAlltokens": i,
                "oriTok": t,
                "subTokLen": toked.__len__(),
                "subToks": toked,
                "pos": pos_tag
            }
        )

    # transfer  to adj nodes
    length = pos
    matrix = np.zeros([length, length], dtype=np.bool)
    # 29 * 29  --> 32 * 32
    assert selected_dfg.shape[0] == len(all_tokens_subtoks)
    for i, col in enumerate(selected_dfg):
        child = [idx for idx, item in enumerate(col) if item]
        # print(child)
        all_tokens_subtoks[i]["children"] = child

    subtokens_list = []
    for ori_item in all_tokens_subtoks:
        pos = ori_item["pos"]
        # print(ori_item["subToks"])
        subtokens_list.extend(ori_item["subToks"])

        for p in pos:
            matrix[p][p] = 1

        # ori_item_child = [ all_tokens_subtoks[c]  for c in ori_item["children"] ]
        ori_item_child = [all_tokens_subtoks[c] for c in ori_item["children"] if all_tokens_subtoks[c] != ori_item]
        for c in ori_item_child:
            # print(c)
            for p in pos:
                matrix[p, c["pos"]] = 1
                # dfg 非对称
                # matrix[c["pos"], p] = 1
        # 将 同一个节点 split 为多个节点之间的边去掉
        for p in pos:
            for pp in pos:
                if p != pp:
                    matrix[p][pp] = 0

    assert len(subtokens_list) == length

    return matrix, subtokens_list


def split_adj_matrix_from_subtokens(selected_adj, mul_view_matrix, code_tokens, all_tokens,
                                    mapping_tgt_tks_to_ast_nodes):
    # selected_adj, mul_view_matrix, code_tokens, all_tokens, mapping_tgt_tks_to_ast_nodes

    key_words = ['instanceof_expression', 'field_access', 'class', '...', 'assert', 'try_with_resources_statement', 'native',
 'labeled_statement', '%=', 'assignment_expression', 'default', '+', '>', 'return', 'inferred_parameters', '<<=',
 'super', 'identifier', '=', '/=', 'annotated_type', 'strictfp', 'yield', 'synchronized_statement', 'abstract',
 'annotation_argument_list', 'case', 'return_statement', '@', ';', 'binary_expression', 'enhanced_for_statement', '}',
 'program', 'dimensions', '>=', '^', ':', '^=', 'double', 'array_type', 'switch_expression', 'final', 'wildcard',
 'throws', 'else', 'scoped_type_identifier', 'object_creation_expression', 'synchronized', '||', '==', 'ERROR',
 'public', '.', 'block', '|', 'void_type', '*', 'switch', 'record', 'parenthesized_expression', 'throw_statement',
 'byte', '[', 'assert_statement', 'int', '++', '--', '!=', '>>=', '|=', 'try_statement', 'while', '+=', 'type_arguments',
 'break_statement', 'array_access', '%', 'class_declaration', 'field_declaration', 'break', '-', '{', 'array_initializer',
 'annotation', 'spread_parameter', 'expression_statement', 'formal_parameter', ',', 'boolean_type', 'cast_expression',
 'catch_type', 'do', 'static', 'marker_annotation', 'resource', 'class_literal', '<<', ']', '!', 'type_identifier',
 'continue_statement', 'float', '&', 'unary_expression', 'floating_point_type', 'finally', '~', 'catch_clause',
 'element_value_array_initializer', 'while_statement', 'do_statement', 'finally_clause', 'variable_declarator', '&&',
 'element_value_pair', 'modifiers', 'for', 'array_creation_expression', ')', 'method_invocation', 'if', 'integral_type',
 'argument_list', 'resource_specification', 'formal_parameters', 'class_body', 'switch_label', 'ternary_expression',
 'catch', 'char', 'catch_formal_parameter', 'switch_block', 'extends', 'private', 'this', '-=', 'try', 'scoped_identifier',
 'throw', '(', 'if_statement', 'update_expression', 'null_literal', '/', 'with', 'short', '?', 'generic_type', '&=',
 'long', 'continue', 'switch_block_statement_group', '<=', '*=', 'new', 'instanceof', 'dimensions_expr', '<', 'protected',
 'local_variable_declaration', 'for_statement', '>>>=']


    all_tokens_subtoks = []
    pos_tag = []
    pos = 0
    for i, t in enumerate(all_tokens):
        if t in key_words:
            toked = [t]
        else:
            toked = python_tokenize(t)
        pos_tag = [p for p in range(pos, pos + len(toked))]

        pos += len(toked)
        # print(i,  t, toked.__len__(),toked, pos_tag)
        # print()

        # if toked.__len__() > 1:
        all_tokens_subtoks.append(
            {
                "idxInAlltokens": i,
                "oriTok": t,
                "subTokLen": toked.__len__(),
                "subToks": toked,
                "pos": pos_tag
            }
        )

    # transfer  to adj nodes
    length = pos
    matrix = np.zeros([length, length], dtype=np.bool)
    # 29 * 29  --> 32 * 32
    assert selected_adj.shape[0] == len(all_tokens_subtoks)
    for i, col in enumerate(selected_adj):
        child = [idx for idx, item in enumerate(col) if item]
        # print(child)
        all_tokens_subtoks[i]["children"] = child

    subtokens_list = []
    for ori_item in all_tokens_subtoks:
        pos = ori_item["pos"]
        # print(ori_item["subToks"])
        subtokens_list.extend(ori_item["subToks"])

        for p in pos:
            matrix[p][p] = 1

        # ori_item_child = [ all_tokens_subtoks[c]  for c in ori_item["children"] ]
        # 不要自己作为 自己的 children [all_tokens_subtoks[c] for c in ori_item["children"] if all_tokens_subtoks[c] != ori_item]
        ori_item_child = [all_tokens_subtoks[c] for c in ori_item["children"] if all_tokens_subtoks[c] != ori_item]
        for c in ori_item_child:
            # print(c)
            for p in pos:
                matrix[p, c["pos"]] = 1
                matrix[c["pos"], p] = 1
        # 将 同一个节点 split 为多个节点之间的边去掉
        for p in pos:
            for pp in pos:
                if p != pp:
                    matrix[p][pp] = 0

    assert len(subtokens_list) == length

    return matrix, subtokens_list



def generate_mv_matrix_java(code, parser):

    tree = parser[0].parse(bytes(code, 'utf8'))

    # code_tokens, dfg_edges, code_snippet_tokens, adj_matrix, mapping_nodes, ast_nodes, all_nodes, tree
    # code_tokens, dfg, code_snippet_tokens, adj, mapping_nodes, ast_nodes, all_nodes, tree
    code_tokens, dfg_edges, code_snippet_tokens, adj_matrix, mapping_nodes, ast_nodes, all_nodes, tree = extract_dataflow(code, parser, lang='java')

    all_nodes_tokens, all_tokens, mapping_tgt_tks_to_ast_nodes, mapping_ast_nodes_to_tgt_tks = asts2tokens_nodes(tree)

    df_edges_in_dfg, df_edges_in_ast = add_dfg_to_adj(code_tokens, dfg_edges, code_snippet_tokens, mapping_nodes,
                                                      ast_nodes)
    statements_edges = extract_statement(tree=tree, all_nodes=all_nodes)

    mul_view_matrix, selected_adj, selected_stm, selected_dfg = combine_multi_view_matrix(adj_matrix, df_edges_in_dfg, df_edges_in_ast, statements_edges,
                                                code_tokens, mapping_tgt_tks_to_ast_nodes, exact_flag=False)

    # mul_view_matrix, selected_adj = combine_multi_view_matrix(adj_matrix, df_edges_in_dfg, df_edges_in_ast, statements_edges,
    #                                             code_tokens, mapping_tgt_tks_to_ast_nodes, exact_flag=False)

    adj, tokens_1 = split_adj_matrix_from_subtokens(selected_adj, mul_view_matrix, code_tokens, all_tokens, mapping_tgt_tks_to_ast_nodes)
    dfg, tokens_1 = split_dfg_matrix_from_subtokens(selected_dfg, mul_view_matrix, code_tokens, all_tokens, mapping_tgt_tks_to_ast_nodes)
    stm, tokens_1 = split_adj_matrix_from_subtokens(selected_stm, mul_view_matrix, code_tokens, all_tokens, mapping_tgt_tks_to_ast_nodes)

    mvm = adj + dfg + stm

    distance_matrix_spllit = get_distance_matrix_from_ast(adj)
    assert distance_matrix_spllit.shape == mvm.shape == adj.shape
    # assert tokens_1 == tokens_2

    assert len(tokens_1) == distance_matrix_spllit.shape[0]


    return adj, mvm, distance_matrix_spllit, tokens_1, dfg, stm




def save_matrix_npy_java():
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

    src_train = dataset['src_train']
    src_dev = dataset['src_dev']
    src_test = dataset['src_test']

    tgt_train = dataset['tgt_train']
    tgt_dev = dataset['tgt_dev']
    tgt_test = dataset['tgt_test']

    print(datetime.datetime.now())

    already = 0
    for key in ['src_train', 'src_dev', 'src_test']:
    # for key in dataset.keys():
        print()
        print(len(dataset[key]), " {} cases are processing ... ".format(key))
        st = datetime.datetime.now()
        print(st)

        dist_npy_file_dir = './java_20230901/distances/'

        mltv_npy_file_dir = './java_20230901/adjacency/'
        mltv_ast_npy_file_dir = './java_20230901/ast/'
        mltv_fl_npy_file_dir = './java_20230901/fl/'
        mltv_dp_npy_file_dir = './java_20230901/dp/'

        subtk_file_dir = './java_20230901/'

        _dirs_ = [dist_npy_file_dir, mltv_npy_file_dir, mltv_ast_npy_file_dir, mltv_fl_npy_file_dir, mltv_dp_npy_file_dir,
                  subtk_file_dir]
        for _dir_ in _dirs_:
            if not os.path.exists(_dir_):
                os.makedirs(_dir_)

        string, guid = [], []
        with open(subtk_file_dir + '{}.token.code'.format(key), 'w', encoding='utf8') as f:
            with open(subtk_file_dir + '{}.token.guid'.format(key), 'w', encoding='utf8') as g:
                for idx, src_raw in enumerate(dataset[key]):
                    uid = already + idx
                    if idx == 10:
                        break
                    if idx % 5000 == 0:
                        print(idx, end='| ')
                    # if idx % 3000 == 0:
                    #     print(idx, end='| ')
                    # print(idx, end=" |")

                    code = src_raw

                    # adj, mvm, distance_matrix_spllit, tokens_1 = generate_mv_matrix_java(code, parser, True)
                    adj, mvm, distance_matrix_spllit, tokens_1, dfg, stm = generate_mv_matrix_java(code, parser)
                    np.savez_compressed(mltv_npy_file_dir + '{}.npy'.format(uid), mvm)
                    np.savez_compressed(mltv_ast_npy_file_dir + '{}.npy'.format(uid), adj)
                    np.savez_compressed(mltv_dp_npy_file_dir + '{}.npy'.format(uid), stm)
                    np.savez_compressed(mltv_fl_npy_file_dir + '{}.npy'.format(uid), dfg)
                    np.savez_compressed(dist_npy_file_dir + '{}.npy'.format(uid), distance_matrix_spllit)
                    string.append(' '.join(tokens_1) + '\n')
                    guid.append(str(uid) + '\n')

                f.writelines(string)
                g.writelines(guid)
                # t.append(datetime.datetime.now())
        already += len(dataset[key])
        # print(st)
        # for tt in t:
        #     print(tt)

    print("Done")

if __name__ == '__main__':
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


    code  =  '''private int currentDepth ( ) { try { Integer oneBased = ( ( Integer ) DEPTH_FIELD . get ( this ) ) ; return oneBased - _NUM ; } catch ( IllegalAccessException e ) { throw new AssertionError ( e ) ; } }'''

    adj, mvm, distance_matrix_spllit, tokens_1, dfg, stm = generate_mv_matrix_java(code, parser)

    save_matrix_npy_java()
    # 2022-09-01 整理代码
    # 这是一个 Java 的预处理过程，适用的代码 NCS、SIT3、SCRIPT
    # 这是最后的java_0725的版本
    print("OK")

