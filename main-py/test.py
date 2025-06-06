import pytest
import sys

sys.path.append(".")

import Operations as Operations
import Property as Property
import Type as Type


@pytest.fixture
def empty_tree():
    return Type.Rb__tree_Null()


@pytest.fixture
def populated_tree():
    t = Type.Rb__tree_Null()
    keys = [10, 7, 18, 2, 8, 15, 25, 1, 3]
    for key in keys:
        t = Operations.default__.insert(t, key)
    return t, set(keys)


# Actual test


def test_insert_empty_tree(empty_tree):
    """Test inserting a single element into an empty tree."""
    t = Operations.default__.insert(empty_tree, 10)

    assert isinstance(t, Type.Rb__tree_Node)
    assert t.key == 10
    assert Property.default__.rootProperty(t)
    assert Property.default__.bstProperty(t)
    assert Property.default__.strongLLRB(t)


def test_insert_multiple_elements(populated_tree):
    t, keys = populated_tree

    assert Property.default__.rootProperty(t)
    assert Property.default__.bstProperty(t)
    assert Property.default__.strongLLRB(t)

    tree_content = Property.default__.contain(t)
    assert set(tree_content.Elements) == keys


def test_rotate_left():
    right_child = Type.Rb__tree_Node(
        Type.Color_Red(), 20, Type.Rb__tree_Null(), Type.Rb__tree_Null()
    )
    h = Type.Rb__tree_Node(Type.Color_Black(), 10, Type.Rb__tree_Null(), right_child)
    rotated_tree = Operations.default__.rotateLeft(h)

    assert rotated_tree.key == 20
    assert isinstance(rotated_tree.color, Type.Color_Black)
    assert isinstance(rotated_tree.left, Type.Rb__tree_Node)
    assert rotated_tree.left.key == 10
    assert isinstance(rotated_tree.left.color, Type.Color_Red)


def test_rotate_right():
    left_child = Type.Rb__tree_Node(
        Type.Color_Red(), 5, Type.Rb__tree_Null(), Type.Rb__tree_Null()
    )
    h = Type.Rb__tree_Node(Type.Color_Black(), 10, left_child, Type.Rb__tree_Null())

    rotated_tree = Operations.default__.rotateRight(h)

    assert rotated_tree.key == 5
    assert isinstance(rotated_tree.color, Type.Color_Black)
    assert isinstance(rotated_tree.right, Type.Rb__tree_Node)
    assert rotated_tree.right.key == 10
    assert isinstance(rotated_tree.right.color, Type.Color_Red)


def test_flip_color():
    left_child = Type.Rb__tree_Node(
        Type.Color_Red(), 5, Type.Rb__tree_Null(), Type.Rb__tree_Null()
    )
    right_child = Type.Rb__tree_Node(
        Type.Color_Red(), 15, Type.Rb__tree_Null(), Type.Rb__tree_Null()
    )
    h = Type.Rb__tree_Node(Type.Color_Black(), 10, left_child, right_child)

    flipped_tree = Operations.default__.flip__color


def test_insert_duplicate_key(populated_tree):
    t, keys = populated_tree

    original_content = Property.default__.contain(t)
    assert set(original_content.Elements) == keys

    # Insert a duplicate key (15 already existed in the populated tree)
    t_after_duplicate_insert = Operations.default__.insert(t, 15)
    new_content = Property.default__.contain(t_after_duplicate_insert)
    assert set(new_content.Elements) == set(original_content.Elements)
    assert Property.default__.strongLLRB(t_after_duplicate_insert)


def test_insert_ascending_order(empty_tree):

    t = empty_tree
    keys = [1, 2, 3, 4, 5, 6, 7]

    for key in keys:
        t = Operations.default__.insert(t, key)
        assert Property.default__.strongLLRB(
            t
        ), f"Tree became invalid after inserting {key}"

    final_content = Property.default__.contain(t)
    assert set(final_content.Elements) == set(keys)


def test_insert_descending_order(empty_tree):
    t = empty_tree
    keys = [10, 9, 8, 7, 6, 5, 4]

    for key in keys:
        t = Operations.default__.insert(t, key)
        assert Property.default__.strongLLRB(
            t
        ), f"Tree became invalid after inserting {key}"

    final_content = Property.default__.contain(t)
    assert set(final_content.Elements) == set(keys)
