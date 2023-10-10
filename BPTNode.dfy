
class BPTNode {
    const ORDER := 5
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


    ghost predicate well()
        reads *
        requires length_ok()
    {
        sorted()&&
        (is_leaf==false ==> (
            child_nb() &&
            child_height_eq() &&
            hierarchy()
        )) &&
        (is_leaf==true ==> (
            leaves_height_eq()
        ))
    }

    // ################ For all nodes ################
    // - min_keys : must contain at least floor(n/2) keys.
    
    ghost predicate sorted()
        //keys are sorted from left two right
        reads this, keys, children
        requires length_ok()
    {
        forall i: int :: 0 <= i < keynum-1 ==> (
            keys[i] < keys[i+1]
        )
    }


    // ################ For internal nodes ################
    ghost predicate child_nb()
        // contains one more child than it has keys. 
        reads this, keys, children
        requires length_ok()
    {
        is_leaf==false ==> (
            (forall i: int :: 0 <= i < keynum ==> (
                keys[i] > 0 && 
                children[i] is BPTNode
            )) &&
            children[keynum] is BPTNode
        )
    }


    ghost predicate child_height_eq()
        // all subtrees must be the same height. 
        reads *
        requires is_leaf==false
        requires length_ok()
        requires child_nb()
    {   
        (forall i: int :: 0 <= i < keynum+1 ==> (
            children[i].height == height -1
        ))
    }
    
    ghost predicate hierarchy()
        // all keys in a given subtree is bounded by surrounding keys in parent node.
        reads * 
        requires is_leaf==false
        requires length_ok()
        requires child_nb()
    {
        forall i: int :: 0 <= i < keynum+1 ==> (
            (forall k :: k in children[i].Contents ==> (
                (i > 0 ==> k >= keys[i-1]) &&
                (i< keynum ==> k <= keys[i])
            ))
        )
    }

    // ################ for leaves ################
    ghost predicate leaves_height_eq()
        // all leaves are at the same distance from the root (always -1).
        reads this
    {
        is_leaf <==> height==-1
    }


    // - linked_leaves : contains extra pointer towards the next leaf.
    // - all_keys_in_leaves : all keys appear in a leaf node.

    ghost predicate length_ok()
        // the keys and children array are well formed
        reads this, children, keys
    {
        keys.Length == ORDER &&
        children.Length == ORDER+1 &&
        keynum < ORDER + 1 &&
        keynum >= 0 
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
        ensures well()
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