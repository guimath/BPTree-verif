include "BPTNode.dfy"

class BPTree {
    ghost var Contents: set<int>
    ghost var Repr: set<object>

    var root: BPTNode?;
    predicate Well()
        reads this, Repr,root 
    {
        this in Repr &&
        (root == null ==> Contents == {}) && 
        (root != null ==> 
            root in Repr && root.Repr <= Repr &&
            root.Well() &&
            Contents == root.Contents)
    }

    constructor Init()
        ensures Well() && fresh(Repr - {this})
        ensures Contents == {}
    { 
        root := null;
        Repr := {this};
        Contents := {};
    } 
    static method spilt_child(parent:BPTNode, pos:int, child:BPTNode) returns (new_child:BPTNode)
        requires 0<=parent.height<=1
        requires 1<=pos <=4 
        requires (parent.newParent()&&pos==1 && child == parent.child_1) || parent.ChildLessWell(pos,child) 
        requires parent !in child.Repr && child in parent.Repr 
        requires parent.height == child.height+1
        //requires pos == 1 ==> child == parent.child_1
        //requires pos == 2 ==> child == parent.child_2
        //requires pos == 3 ==> child == parent.child_3
        //requires pos == 4 ==> child == parent.child_4 
        requires child.Valid() && child.LessWell() 
        requires parent.keynum<=3
        requires child.is_leaf==true ==> child.keynum == 5 
        requires child.is_leaf==false ==> child.child_5 != null
        requires parent.is_leaf == false 
        requires (1<= pos <= parent.keynum+1 )
        modifies parent, child   
        ensures child.Well() && parent.LessWell() && new_child.Well()
        ensures parent.keynum<=3 ==> parent.Well() 
        ensures parent.keynum == old(parent.keynum)+1
        ensures parent.Contents == old(parent.Contents)
    {
         
        assert pos == 2 ==>(forall y :: y in child.Contents ==> y >= parent.key_1);
        new_child := new BPTNode.Init(); 
        new_child.is_leaf := child.is_leaf; 
        new_child.height := child.height;
        var new_key:=0;
        //assert parent.Valid();
        assert ((parent.child_1 != null && pos!=1) ==> parent.child_1.Well());
        assert ((parent.child_2 != null && pos!=2) ==> parent.child_2.Well());
        assert ((parent.child_3 != null && pos!=3) ==> parent.child_3.Well());
        assert ((parent.child_4 != null && pos!=4) ==> parent.child_4.Well());
        if child.is_leaf == true
        { 
            new_child.key_1 := child.key_4;
            new_child.key_2 := child.key_5;
            child.key_4:= 0;
            child.key_5:= 0;
            new_child.keynum:=2;
            child.keynum:=3;
            new_key:=new_child.key_1;

            new_child.Contents := {new_child.key_1,new_child.key_2};
            child.Contents := {child.key_1,child.key_2,child.key_3};
            assert child.Well();
        }
        else 
        {
            new_child.key_1 := child.key_4;
            new_key := child.key_3;
            child.key_3:= 0;
            child.key_4:= 0;

            new_child.keynum:=1;
            child.keynum:=2;

            new_child.child_1 := child.child_4;
            new_child.child_2 := child.child_5;
            child.child_4 := null;
            child.child_5 := null;

            new_child.Repr := {new_child}+new_child.child_1.Repr+new_child.child_2.Repr;
            child.Repr := {child}+child.child_1.Repr+child.child_2.Repr+child.child_3.Repr;

            new_child.Contents := new_child.child_1.Contents+new_child.child_2.Contents;
            child.Contents := child.child_1.Contents+child.child_2.Contents+child.child_3.Contents;
            assert child.Valid();
            assert child.Well();
            assert new_child.Well(); 
        }     
        assert parent == old(parent);     
        assert pos!=1 ==> child!in parent.child_1.Repr;   
        assert child.Valid();
        assert child.Well();
        assert new_child.Well();
        assert ((parent.child_1 != null && pos!=1) ==> parent.child_1.Well());
        assert ((parent.child_2 != null && pos!=2) ==> parent.child_2.Well());
        assert ((parent.child_3 != null && pos!=3) ==> parent.child_3.Well());
        assert ((parent.child_4 != null && pos!=4) ==> parent.child_4.Well());
        if pos == 4
        {
            assert parent.keynum>3 ==> parent.key_3<= new_key<= parent.key_4;
            assert parent.keynum==3 ==> parent.key_3<= new_key;
            parent.child_5 := new_child;
            parent.child_4 := child;
             
            parent.key_4 := new_key;
            assert parent.keynum ==3;
            assert parent.child_1.Well(); 
        }
        else if pos == 3
        {
            assert parent.keynum>2 ==> parent.key_2<= new_key<= parent.key_3;
            assert parent.keynum==2 ==> parent.key_2<= new_key;
            parent.child_5 := parent.child_4;
            parent.child_4 := new_child;
            parent.child_3 := child;
            
            parent.key_4 := parent.key_3;
            parent.key_3 := new_key;
            assert parent.child_1.Well();
        }
        else if pos == 2
        {
            assert parent.keynum>1 ==> parent.key_1<= new_key<= parent.key_2;
            assert parent.keynum==1 ==> parent.key_1<= new_key;
            assert parent.child_1.Well();
            parent.child_5 := parent.child_4;
            parent.child_4 := parent.child_3;
            parent.child_3 := new_child; 
            parent.child_2 := child; 

            parent.key_4 := parent.key_3;
            parent.key_3 := parent.key_2;
            parent.key_2 := new_key; 
            assert parent.child_1.Well();
        }
        else if pos == 1
        {
            assert parent.keynum>0 ==> new_key<= parent.key_1;
            parent.child_5 := parent.child_4;
            parent.child_4 := parent.child_3;
            parent.child_3 := parent.child_2;
            parent.child_2 := new_child;
            parent.child_1 := child;

            parent.key_4 := parent.key_3;
            parent.key_3 := parent.key_2;
            parent.key_2 := parent.key_1;
            parent.key_1 := new_key;
            assert parent.child_1.Well();
        }
        parent.keynum := parent.keynum+1;
        if parent.keynum ==1
        {
            parent.Contents := parent.child_1.Contents + parent.child_2.Contents;
            parent.Repr := {parent} + parent.child_1.Repr + parent.child_2.Repr;
            assert parent.child_1.Well();
            assert parent.child_2.Well();
            assert parent.Valid();
        }
        else if parent.keynum ==2
        {
            parent.Contents := parent.child_1.Contents + parent.child_2.Contents + parent.child_3.Contents;
            parent.Repr := {parent} + parent.child_1.Repr + parent.child_2.Repr + parent.child_3.Repr;
        /*    assert parent.child_1.Well();
            assert parent.child_2.Well(); 
            assert parent.child_3.Well();*/
            //assert parent.Valid();  
        }
        else if parent.keynum ==3
        {
            parent.Contents := parent.child_1.Contents + parent.child_2.Contents + parent.child_3.Contents + parent.child_4.Contents;
            parent.Repr := {parent} + parent.child_1.Repr + parent.child_2.Repr + parent.child_3.Repr + parent.child_4.Repr;
        /*    assert parent.child_1.Well();
            assert parent.child_2.Well(); 
            assert parent.child_3.Well();
            assert parent.child_4.Well();
            assert parent.Valid();*/
        }
        else if parent.keynum ==4
        {
            parent.Contents := parent.child_1.Contents + parent.child_2.Contents + parent.child_3.Contents + parent.child_4.Contents + parent.child_5.Contents;
            parent.Repr := {parent} + parent.child_1.Repr + parent.child_2.Repr + parent.child_3.Repr + parent.child_4.Repr + parent.child_5.Repr;
         /*   assert parent.child_1.Well();
            assert parent.child_2.Well(); 
            assert parent.child_3.Well();
            assert parent.child_4.Well(); 
            assert parent.child_5.Well();
            assert parent.Valid();*/
        }
    }
/*
    static method refresh(node:BPTNode)
        requires node.is_leaf == false
        requires node.keynum>=1 ==> (node.child_1!=null && node.child_1.Valid())
        requires node.keynum>=1 ==> (node.child_2!=null && node.child_2.Valid())
        requires node.keynum>=2 ==> (node.child_3!=null && node.child_3.Valid())
        requires node.keynum>=3 ==> (node.child_4!=null && node.child_4.Valid())
        requires node.keynum>=4 ==> (node.child_5!=null && node.child_5.Valid())
        modifies node
        ensures node.Valid()
    {
        if node.keynum ==1
        {
            node.Contents := node.child_1.Contents + node.child_2.Contents;
            node.Repr := {node} + node.child_1.Repr + node.child_2.Repr;
        }
        else if node.keynum ==2
        {
            node.Contents := node.child_1.Contents + node.child_2.Contents + node.child_3.Contents;
            node.Repr := {node} + node.child_1.Repr + node.child_2.Repr + node.child_3.Repr;
        }
        else if node.keynum ==3
        {
            node.Contents := node.child_1.Contents + node.child_2.Contents + node.child_3.Contents + node.child_4.Contents;
            node.Repr := {node} + node.child_1.Repr + node.child_2.Repr + node.child_3.Repr + node.child_4.Repr;
        }
        else if node.keynum ==4
        {
            node.Contents := node.child_1.Contents + node.child_2.Contents + node.child_3.Contents + node.child_4.Contents + node.child_5.Contents;
            node.Repr := {node} + node.child_1.Repr + node.child_2.Repr + node.child_3.Repr + node.child_4.Repr + node.child_5.Repr;
        }
    } 
*/




    static method insert_helper(father:BPTNode?, node:BPTNode?, x:int, pos:int) returns (new_node:BPTNode)
        requires father!=null ==> father.height<=3
        requires node!=null ==> node.height<=3
        requires (node!=null && father!=null) ==> (node in father.Repr&& father.height == node.height+1 && father !in node.Repr)
        requires node == null || (node.Well())
        requires node == null ==> father ==null
        requires father == null ==> pos==1
        requires father!=null ==> father.keynum+1>=pos>=1
        requires father!=null ==> father.Well()
        requires father!=null ==> father.is_leaf==false
        requires (father!=null&& pos ==1) ==> x<=father.key_1
        requires (father!=null&& pos ==2) ==> (x>=father.key_1&& (father.keynum>=2 ==> x<=father.key_2))
        requires (father!=null&& pos ==3) ==> (x>=father.key_2&& (father.keynum>=3 ==> x<=father.key_3))
        requires (father!=null&& pos ==4) ==> (x<=father.key_4)
        modifies if node!= null then node.Repr else {}
        modifies father
        //ensures father== null ==> new_node.Well() 
        ensures new_node.Well()
        ensures father !=null ==> (father.Contents == old(father.Contents+{x}))
        ensures node !=null ==> node.Well()
        ensures node == old(node)
        ensures father == old(father)
        ensures father!=null ==> father.LessWell()
        decreases if node == null then {} else node.Repr 
    {
        new_node := new BPTNode.Init();

        if node == null {
            new_node.key_1 := x;
            new_node.Contents := new_node.Contents+{x};
            new_node.keynum :=1;
            assert new_node.Contents == {new_node.key_1};
            assert (new_node.keynum==1 <==> new_node.Contents =={new_node.key_1});
            assert new_node.Well();

        } else if node.is_leaf == true { 
            
            assert node.Well();  
            if node.keynum==4 && x>= node.key_4
            {
                node.key_5:=x;
                assert node.sortkey();  
            }
            else if  node.keynum>=3 && x>= node.key_3
            {  
                node.key_5 := node.key_4; 
                node.key_4:=x;
                assert node.sortkey();  
            }
            else if  node.keynum>=2 && x>= node.key_2
            {
                node.key_5 := node.key_4;
                node.key_4 := node.key_3;
                node.key_3:=x;
                assert node.sortkey();  
            }
            else if  node.keynum>=1 && x>= node.key_1
            {
                node.key_5 := node.key_4;
                node.key_4 := node.key_3;
                node.key_3 := node.key_2;
                node.key_2:=x;
                assert node.sortkey();  
            }
            else 
            {
                node.key_5 := node.key_4;
                node.key_4 := node.key_3;
                node.key_3 := node.key_2;
                node.key_2 := node.key_1;
                node.key_1:=x;
                assert node.sortkey();  
            }
            node.keynum := node.keynum+1;
            node.Contents := node.Contents +{x};
            new_node:= node;
            if father!= null
            {
                father.Contents := father.Contents+{x};
            }
            assert node.ContainingKey(); 
            assert node.Valid();
            assert node.sortkey();  
            assert node.LessWell();
            assert father!= null ==> (father.Contents == old(father.Contents)+{x}&&father.Valid());
            assert (node.keynum==5 && node.is_leaf==true) ==> node.LessWell();
            assert (node.keynum< 5 && node.is_leaf==true) ==> node.LessWell();
        } else {
            assert node.is_leaf == false && node.Valid();
            assert father!=null ==> father.sortkey();
            assert father!=null ==> father.Valid(); 
            if node.keynum==3 && x>= node.key_3
            {
                new_node := insert_helper(node,node.child_4,x,4);
                new_node:=node;
            }
            else if  node.keynum>=2 && x>= node.key_2
            {
                new_node := insert_helper(node,node.child_3,x,3);
                new_node:=node;
            }
            else if  node.keynum>=1 && x>= node.key_1
            {
                new_node := insert_helper(node,node.child_2,x,2);
                new_node:=node;
                
            }
            else 
            {
                new_node := insert_helper(node,node.child_1,x,1);
                new_node:=node;
            }
            if father.keynum ==1
            {
                father.Contents := father.child_1.Contents + father.child_2.Contents;
                father.Repr := {father} + father.child_1.Repr + father.child_2.Repr;
            }
            else if father.keynum ==2
            {
                father.Contents := father.child_1.Contents + father.child_2.Contents + father.child_3.Contents;
                father.Repr := {father} + father.child_1.Repr + father.child_2.Repr + father.child_3.Repr;
            }
            else if father.keynum ==3
            {
                father.Contents := father.child_1.Contents + father.child_2.Contents + father.child_3.Contents + father.child_4.Contents;
                father.Repr := {father} + father.child_1.Repr + father.child_2.Repr + father.child_3.Repr + father.child_4.Repr;
            }
            else if father.keynum ==4
            {
                father.Contents := father.child_1.Contents + father.child_2.Contents + father.child_3.Contents + father.child_4.Contents + father.child_5.Contents;
                father.Repr := {father} + father.child_1.Repr + father.child_2.Repr + father.child_3.Repr + father.child_4.Repr + father.child_5.Repr;
            }
            //if father!= null
            //{
            //    father.Contents := father.Contents+{x};
            //}
            new_node := node;
            assert node.Valid(); 
            assert node.LessWell();
            assert node.Contents == old(node.Contents)+{x};
            assert father!=null ==> father.keynum==old(father.keynum);
            assert father!=null ==> father.sortkey();
            assert father!=null ==> father.Valid(); 
            assert father!=null ==> father.ChildLessWell(pos,node);
            assert (node.keynum==4 && node.is_leaf==false) ==> node.LessWell();
            assert (node.keynum< 4 && node.is_leaf==false) ==> node.Well();
        }
        assert node==null || (node.keynum==4 && node.is_leaf==false) || (node.keynum==5 && node.is_leaf==true) || node.Well();
        if node!=null && ((node.keynum==4 && node.is_leaf==false)||(node.keynum==5 && node.is_leaf==true))
        {
            var new_father :=new BPTNode.Init();
            var newchild :=new BPTNode.Init();
            assert new_father.key_1==0;
            assert new_father.key_2==0;
            assert new_father.key_3==0;
            assert new_father.key_4==0;
            if father == null
            {
                assert node.Valid();
                new_father.height := node.height+1;
                new_father.is_leaf := false;
                new_father.child_1 := node;
                new_father.Contents := new_father.Contents+node.Contents;
                new_father.Repr := new_father.Repr+{node}+node.Repr;
                new_node := new_father;

                assert new_father.newParent();
                assert new_father.Contents == node.Contents;
                assert new_father.keynum==0;
                newchild := spilt_child(new_father, pos, node);
                assert new_father.keynum<=3;
                assert new_father.Well();
                assert new_node.Well();
            }
            else
            {
                new_father := father;
                assert new_father.ChildLessWell(pos,node);
                newchild := spilt_child(new_father, pos, node);
                assert new_node.Well();
            } 
            assert new_father.LessWell();
            assert node.Well();
            assert newchild.Well();
        }
        assert node==null || node.Well();
    }
    method Insert(val: int)
        requires Well()
        requires root!=null ==> root.height<=2
        modifies Repr    
        ensures Well()
        ensures Contents == old(Contents) + {val}
    {
        print("\n--Inserting ");
        print(val);
        print("\n");
        root := insert_helper(null, root, val, 1);
        assert root.Well();
        Contents := root.Contents;
        Repr := root.Repr + {this};
    }

    function method Find(val: int): bool
        requires Well()
        reads Repr
        ensures Find(val) <==> (val in Contents)
    {
        root != null && find_helper(val, root)
    }

    function method find_helper(val: int, node:BPTNode): bool
        requires node.Well()
        reads node.Repr
        ensures find_helper(val, node) <==> (val in node.Contents)
        decreases node.Repr 
    { 
        assert node.sortkey();
        if node.is_leaf == true  then 
        ((val == node.key_1 && node.keynum>=1) || (val == node.key_2 && node.keynum>=2)  ||(val == node.key_3 && node.keynum>=3)  ||(val == node.key_4 && node.keynum>=4) )
        else if node.keynum>0 && node.key_1>val && node.is_leaf == false then
        find_helper(val, node.child_1) 
        else if ((node.keynum>1 && node.key_2>val) || (node.keynum==1 && node.key_1<=val)) && node.is_leaf == false then
        find_helper(val, node.child_2) 
        else if ((node.keynum>2 && node.key_3>val) || (node.keynum==2 && node.key_2<=val)) && node.is_leaf == false then
        find_helper(val, node.child_3) 
        else if node.keynum>2 && node.key_3<=val && node.is_leaf == false then
        find_helper(val, node.child_4) 
        else 
        false 
         
    }


/*    static method get_height(node:BPTNode?) returns (height:int) {
        if(node == null) {
            height := -1;
        } else {
            height := node.height;
        }
    }*/


    


    /*
    method Print()
        requires root != null ==> root.Valid();
    {
        print("\n----Tree>>>>");
        print_tree_recursive(root);
        print("<<<<Tree----");
    }
    static method print_tree_recursive(node:BPTNode?)
        requires node == null || (node.Valid())
        decreases if node == null then {} else node.Repr
    {
        if(node != null) {
            var low:=0;
            print(node.height);
            print(":(");
            print(node.key_1);
            print(" ");
            print(node.key_2);
            print(" ");
            print(node.key_3);
            print(" ");
            print(node.key_4);
            
            print(")\n");
            if node.child_1!=null
            {
                print_tree_recursive(node.child_1);
            }
            if node.child_2!=null
            {
                print_tree_recursive(node.child_2);
            }
            if node.child_3!=null
            {
                print_tree_recursive(node.child_3);
            }
            if node.child_4!=null
            {
                print_tree_recursive(node.child_4);
            }
        }
    }
    */ 

} 