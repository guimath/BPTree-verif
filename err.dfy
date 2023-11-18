include "BPTNode.dfy"


static method FindHelper(node: BPTNode, val: int) returns (inTree: bool) // verifies correct in under 100 seconds
        requires node.Valid()
        ensures node.ContainsVal(val) <==> inTree
        decreases node.Repr
    {        
        if node.keyNum > 0 && !node.isLeaf {
            var idx := node.keyNum;
            for i := 0 to node.keyNum 
                invariant 0 <= i <= node.keyNum 
            {
                if val == node.keys[i]  {
                    assert node.ContainsVal(val); // Having this assert as well as the second one results in timeout
                    return true; // verifies assert node.ContainsVal(val);
                }
                if val < node.keys[i] {
                    idx := i;
                    break;
                }
            }   
            // assert node.ContainsVal(val) <==> inTree; //This assert doesn't complete
            return false; // Why success ?
        }
        return false;
    }