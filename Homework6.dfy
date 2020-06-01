datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>
{
	match tree
    case Leaf() => Nil
    case Node (left, right, e) => append (flatten (left),Cons (e, flatten (right)))
}

function append<T>(xs:List<T>, ys:List<T>):List<T>
ensures xs == Nil ==> append(xs,ys) == ys
ensures ys == Nil ==> append(xs,ys) == xs


{
	match(xs)
	case Nil => ys
	case Cons(x, xs') =>  Cons(x, append(xs', ys))
}

function listContains<T>(xs:List<T>, element:T):bool
//ensures listContains(append(xs, ys), element) == (listContains(xs, element) ||  listContains(ys, element))
{
	match(xs)
	case Cons(x, xs') => x==element || listContains(xs', element) 
	case Nil => false
}

function treeContains<T>(tree:Tree<T>, element:T):bool
{
	match(tree)
    case Leaf => false
    case Node(t1, t2, x) => treeContains(t1, element) || treeContains(t2, element) || x== element
}

//listContains(append(xs, ys), element) == (listContains(xs, element) ||  listContains(ys, element))
lemma sameElements<T>(tree:Tree<T>, element:T)

ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
//ensures listContains(append(xs, ys), element) == (listContains(xs, element) ||  listContains(ys, element))
{
	match (tree)
    case Leaf => {}
    case Node(l,r,e) =>{
        calc{
            treeContains(tree, element);
            == treeContains(Node(l,r,e), element);
            ==treeContains(l,element) || treeContains(r,element) || e==element;
            ==listContains(flatten(l), element) || listContains(flatten(r), element) || e==element ;   
            ==  listContains(flatten(l), element) || listContains(Cons(e,flatten(r)),element);
            =={ listcontain_as(flatten(l),Cons(e,flatten(r)),element);}
            listContains(append(flatten(l),Cons(e,flatten(r))),element) ;

     
            

        }
    }
    }


lemma listcontain_as<T>(xs:List<T>, ys:List<T>, element:T)

 ensures listContains(append(xs, ys), element) == (listContains(xs, element) ||  listContains(ys, element))
 //ensures (listContains(flatten(l), element) || listContains(flatten(r), element) || (e==element)) ==(listContains(Cons(e, append(flatten(l),flatten(r))),element))
{
match xs
    case Nil => {}
    case Cons(x,xs') => {
        
        calc {
            listContains(append(xs,ys),element);
            == listContains(append(Cons(x,xs'),ys),element);
            == listContains(Cons(x,append(xs',ys)),element);
            == (element==x) || listContains(append(xs',ys),element);
            == { listcontain_as(xs',ys,element); }
               (element==x) || listContains(xs',element) || listContains(ys,element);
            == listContains( Cons(x,xs'),element)  || listContains(ys,element);
            == listContains( xs,element)           || listContains(ys,element);
        }
    }
}


ghost method appendAssociative<T>(xs:List<T>, ys:List<T>, zs:List<T>)
ensures append(xs,  append(ys,zs)) == append( append(xs,ys),   zs)
{
    match xs
    case Nil => {}
    case Cons(x,xs') => {
        calc {
            append(xs,  append(ys,zs));
            == append(Cons(x,xs'),  append(ys,zs));
            == Cons(x,append(xs',  append(ys,zs)));
            == { appendAssociative(xs',ys,zs); 
                 assert append(xs',  append(ys,zs)) == append( append(xs',ys),   zs);
               }
               Cons(x, append( append(xs',ys),   zs) );
            == append( Cons(x, append(xs',ys)),   zs);   
            == append( append(Cons(x, xs'),ys),   zs);   
            == append( append(   xs       ,ys),   zs);   

        }
    }
}