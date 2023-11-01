include "BPTNode.dfy"

class BPTree {
    var root: BPTNode?

    // ghost set for verifivation
    ghost var Contents: set<int> 
    ghost var Repr: set<BPTNode>

    constructor Init()
 //       ensures Well() && 
        ensures fresh(Repr - {this})
        ensures Contents == {}
    { 
        root := null;
        Repr := {this};
        Contents := {};
    } 
}