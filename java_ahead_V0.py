
import numpy as np
from soupsieve import select
from tree_sitter import Language, Parser
from java_preprocessing import read_source_files
from utils import remove_comments_and_docstrings, tree_to_token_index, index_to_code_token, tree_to_variable_index, tree_to_token_index_pro
import itertools
import networkx as nx
import datetime
import re

from DFG import DFG_java

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


def save_matrix_npy():
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

    # src_raw_train, src_raw_dev, src_raw_test
    # src_raw_lsit = []

    already = 0
    for key in dataset.keys():
        print()
        print(len(dataset[key]), " {} cases are processing ... ".format(key))
        st = datetime.datetime.now()
        print(st)

        dist_npy_file_dir = './python_0626/distances/'

        mltv_npy_file_dir = './python_0626/adjacency/'

        subtk_file_dir = './python_0626/'

        string, guid = [], []
        with open(subtk_file_dir + '{}.token.code'.format(key), 'w', encoding='utf8') as f:
            with open(subtk_file_dir + '{}.token.guid'.format(key), 'w', encoding='utf8') as g:
                for idx, src_raw in enumerate(dataset[key]):
                    uid = already + idx
                    # if idx == 50:
                    #     break
                    if idx % 5000 == 0:
                        print(idx, end='| ')
                    # if idx % 3000 == 0:
                    #     print(idx, end='| ')
                    # print(idx, end=" |")
                    code = src_raw.replace(' DCNL DCSP ', '\n\t'). \
                        replace(' DCNL  DCSP ', '\n\t'). \
                        replace(' DCNL   DCSP ', '\n\t'). \
                        replace(' DCNL ', '\n').replace(' DCSP ', '\t')

                    adj, mvm, distance_matrix_spllit, tokens_1 = generate_mv_matrix_v1(code, parser, True)
                    np.savez_compressed(mltv_npy_file_dir + '{}.npy'.format(uid), mvm)
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
    code = """

    def sample():
        a = random()
        if a % 2 == 0:
            b = a + 1
            print(b)

    """
    code = '''
    def _tosequence(X):
        if isinstance(X, Mapping):
            return [X]
        else:
            return tosequence(X)
    '''
    print("OK")
    #
    #
    code = """def filepath_to_uri(path): DCNL  DCSP if (path is None): DCNL DCSP  DCSP return path DCNL DCSP return urllib.quote(smart_str(path).replace('\\', '/'), safe="/~!*()'")"""
    # code = """def url_filename(url): DCNL  DCSP match = upload_title_re.match(url) DCNL DCSP if match: DCNL DCSP  DCSP return match.group('filename') DCNL DCSP else: DCNL DCSP  DCSP return url"""
    # code = """def follow_link(connection, link): DCNL  DCSP if link: DCNL DCSP  DCSP return connection.follow_link(link) DCNL DCSP else: DCNL DCSP  DCSP return None"""
    # code = """def escape(s): DCNL  DCSP if (s is None): DCNL DCSP  DCSP return '' DCNL DCSP assert isinstance(s, basestring), ('expected DCSP %s DCSP but DCSP got DCSP %s; DCSP value=%s' % (basestring, type(s), s)) DCNL DCSP s = s.replace('\\', '\\\\') DCNL DCSP s = s.replace('\n', '\\n') DCNL DCSP s = s.replace(' DCTB ', '\\t') DCNL DCSP s = s.replace(',', ' DCTB ') DCNL DCSP return s"""
    adj, mvm, distance_matrix_spllit, tokens_1 = generate_mv_matrix_v1(code, parser, True)
    print()

    save_matrix_npy()
