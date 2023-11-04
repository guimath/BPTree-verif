# BPTree-verif
B+ Tree data structure formal verification using [dafny](https://dafny.org/)

Project led by Ivona Martinovic & Guilhem Mathieux (@guimath) for the CS6271 (advanced topics in software engineering) class at NUS
## Data structure description 

B+ tree is a specialized variant of the B-tree data structure characterized by distinctive organization of data. Much like the conventional B-trees, B+ trees are inherently balanced, ordered and exhibit n-ary tree properties.

Main difference with B trees is that data in B+ trees is stored exclusively in leaf nodes (linked list).

We define the order $n$ of B+ tree as the maximum amount of keys an internal node can have.  

Example of a rank 2 B+ tree :
![B+ tree of rank 2](img/Bplustree_order2.jpg)

## Invariants that must be maintained

For a tree of rank n

#### For all nodes 
- MinKeys : must contain at least floor(n/2) keys.
- Sorted : keys are Sorted from left two right
- LeavesHeightEq : a node has a height value of -1 if and only if it is a leaf

#### For internal nodes
- ChildNum : contains one more child than it has keys. 
- ChildHeightEq : all subtrees must be the same height. 
- Hierarchy : all keys in a given subtree are bounded by surrounding keys in parent node (lower key < subtree keys <= higher keys)
- NonCyclical : no node can be contain cyclical link   
#### for leaves
- LinkedLeaves : contains extra pointer towards the next leaf.
- AllKeysInLeaves : all keys appear in a leaf node.

## for root 

- MinRoot : If the root node is an internal node, it must contain at least 2 children.

All these invariants are defined as ghost predicates in the [BPTNode.dfy](BPTNode.dfy) file