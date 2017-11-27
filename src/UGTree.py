## The trees relating Guard Sets to User Sets

import pytest
import random

class Branch(object):
    __slots__ = ["children"]

    def __init__(self, children):
        self.children = children

class Leaf(object):
    __slots__ = ["content"]
    
    def __init__(self, content):
        self.content = content

class UGTree(object):
    """ The data structure that keep track of the positon of 
    each Guard Sets and its relation to the User Groups and Users"""

    def __init__(self):
        self.root = None

    def new_naive_position(self):
        return [random.choice([0,1]) for _ in range(64)]

    def insert_GS(self, position, GS):
        if self.root == None:
            self.root = Leaf(GS)
            return

        def _insert(rest_tree, rest_position, GS):
            if isinstance(rest_tree, Branch):
                next_tree = rest_tree.children[rest_position[0]]
                next_position = rest_position[1:]
                assert len(next_position) > 0

                # Patch the tree with the new branch
                ret = _insert(next_tree, next_position, GS)
                if ret:
                    rest_tree.children[rest_position[0]] = ret
                
                return rest_tree
            else:
                assert isinstance(rest_tree, Leaf)
                ## Convention: old goes to 0
                return Branch([rest_tree, Leaf(GS)])

        self.root = _insert(self.root, position, GS)

    def _count(self, rest_tree):
        if isinstance(rest_tree, Branch):
            count = 0
            count += self._count(rest_tree.children[0])
            count += self._count(rest_tree.children[1])
            return count
        else:
            assert isinstance(rest_tree, Leaf)
            return 1

    def count(self):
        return self._count(self.root)

    def get_list(self):
        if self.root == None:
            return []

        def _list_nodes(rest_tree, pos, big_list):
            if isinstance(rest_tree, Branch):
                _list_nodes(rest_tree.children[0], pos+[0], big_list)
                _list_nodes(rest_tree.children[1], pos+[1], big_list)
            else:
                assert isinstance(rest_tree, Leaf)
                big_list += [(pos, rest_tree)]

        big_list = []
        _list_nodes(self.root, [], big_list)

        return big_list

    def to_string(self):
        big_list = self.get_list()
        
        s = ""
        for (pos, node) in big_list:
            s += "%s Leaf(%s)\n" % (pos, node.content)
        return s

    def delete_GS(self, position):
        
        if self.root == None:
            raise Exception("Nonthing to delete. Tree empty.")

        if isinstance(self.root, Leaf):
            deleted = self.root
            self.root = None
            return deleted

        def _delete_GS(rest_tree, rest_position):
            if isinstance(rest_tree, Branch):
                next_tree = rest_tree.children[rest_position[0]]
                
                if isinstance(next_tree, Branch):
                    next_position = rest_position[1:]
                    sub_tree, deleted_child = _delete_GS(next_tree, next_position)
                    rest_tree.children[rest_position[0]] = sub_tree
                    return rest_tree, deleted_child

                ## We are about to kill the child!
                the_other_child = rest_tree.children[1 - rest_position[0]]
                deleted_child = rest_tree.children[rest_position[0]]

                if isinstance(the_other_child, Leaf):
                    return the_other_child, deleted_child

                if isinstance(the_other_child, Branch):
                    pos = [1]*100
                    tree, replacement = _delete_GS(the_other_child, pos)

                    ## Replace the deleted node with its replacement
                    rest_tree.children[rest_position[0]] = replacement
                    rest_tree.children[1 - rest_position[0]] = tree

                    return rest_tree, deleted_child
                    
            else:
                raise Exception("Should never get here!")

        new_tree, deleted = _delete_GS(self.root, position)
        self.root = new_tree
        return deleted
