
class BPTNode {
    
    // array of length ORDER
    var keys: array<int>
    // array of length ORDER + 1
    var children: array<BPTNode?>
    // number of keys active
    var keynum: int
    // height
    var height: int
    // is leaf
    var is_leaf: bool 

    // ghost set for verifivation
    ghost var Contents: set<int> 
    ghost var Repr: set<BPTNode>


// #### For all nodes 
// - min_keys : must contain at least floor(n/2) keys.

    // #### For internal nodes
    ghost predicate child_nb()
        // contains one more child than it has keys. 
        reads this, keys, children
        requires is_leaf==false
        requires length_ok()
    {
        (forall i: int :: 0 <= i < keynum ==> (
            keys[i] > 0 && 
            children[i] is BPTNode
        )) &&
        children[keynum] is BPTNode
        // why ?
    }


    ghost predicate child_height_eq()
        reads *
        requires is_leaf==false
        requires length_ok()
        requires child_nb()
    {   
        (forall i: int :: 0 <= i < keynum ==> (
            children[i].height == height -1
        ))
    }
// all subtrees must be the same height. 
// - hierarchy : all keys in a given subtree is bounded by surrounding keys in parent node.
// 
// #### for leaves
// - leaves_height_eq : all leaves are at the same distance from the root (always -1).
// - linked_leaves : contains extra pointer towards the next leaf.
// - sorted : keys are sorted from left two right
// - all_keys_in_leaves : all keys appear in a leaf node.

    ghost predicate length_ok()
        // the keys and children array are well formed
        reads this, children, keys
    {
        keys.Length == ORDER &&
        children.Length == ORDER+1 &&
        keynum <= ORDER
    }

    ghost predicate empty()
        // the keys and children array are empty
        requires length_ok()
        reads this, children, keys
    {
        (forall i: int :: 0 <= i < ORDER ==> (
            children[i]==null &&
            keys[i]==0
        )) &&
        children[ORDER] == null
    }

    constructor init()
        ensures children.Length == ORDER + 1
        ensures keys.Length == ORDER
        ensures keynum==0
        ensures height==-1
        ensures is_leaf==true
        ensures empty()
        //ensures Valid() && Well() && fresh(Repr - {this})
        ensures Contents == {}
        ensures Repr == {this}

    {
        is_leaf := true;
        height := -1;
        keynum := 0;
        Contents := {};
        Repr := {this};
        children := new BPTNode?[ORDER + 1][null, null, null, null, null, null];
        keys := new int[ORDER][0, 0, 0, 0, 0];
        // Hardcoded rather than loop because weird error :
        // "in the first division of the constructor body (before 'new;'), 
        // 'this' can only be used to assign to its fields"
        // When running this loop
        // for i := 0 to ORDER - 1 {
        //     keys[i] := 0;
        //     children[i] := null;
        // }
        // children[ORDER] := null;


    }

}