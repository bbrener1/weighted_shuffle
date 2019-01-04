extern crate num_traits;
extern crate rand;

use num_traits::{Zero,zero,Signed};
use num_traits::cast::{FromPrimitive,ToPrimitive,NumCast};
use std::ops::{Add,AddAssign,Sub,SubAssign,Mul};
use std::convert::From;
use std::mem::swap;
use std::fmt::Debug;
use std::cmp::min;
use rand::random;
use rand::distributions::{Distribution,Standard};

#[derive(Debug)]
pub struct WeightBalancedSearchTree<K,V> {
    root: Option<usize>,
    arena: Vec<STNode<K,V>>,
    indecies: Vec<usize>,
}

#[derive(Debug)]
struct STNode<K,V> {
        parent: Option<(bool,usize)>,
        key: K,
        value: V,
        left_sum: K,
        right_sum: K,
        left:Option<usize>,
        right:Option<usize>,
}

impl<K: Zero,V> STNode<K,V> {
    pub fn new(k:K,v:V) -> STNode<K,V> {
        STNode {
            parent: None,
            key: k,
            value: v,
            left_sum: zero(),
            right_sum: zero(),
            left: None,
            right: None
        }
    }

    pub fn children(&self) -> Vec<usize> {
        vec![self.left,self.right].into_iter().flat_map(|x| x.into_iter()).collect()
    }
}



// struct STLeaf<K,V> {
//     key: K,
//     value: V,
// }
//
// enum Element<K,V> {
//     Node(STNode<K,V>),
//     Leaf(STLeaf<K,V>)
// }
//
// impl Element<K,V> {
//     pub fn new_node(k:K) -> Element {
//         let node = STNode
//     }
// }

impl<K,V> WeightBalancedSearchTree<K,V>
    where
        K: PartialOrd + Sub<K,Output=K> + Add<K,Output=K> + AddAssign<K> + SubAssign<K> + ToPrimitive + NumCast + Zero + Signed + Copy + Debug,
        V: Debug + Copy,
        Standard: Distribution<K>,
{

    pub fn index_tree(weights:Vec<K>) -> WeightBalancedSearchTree<K,usize> {
        let mut tree = WeightBalancedSearchTree::empty();
        // eprintln!("{:?}",tree);
        for (v,k) in weights.into_iter().enumerate() {
            // eprintln!("{:?}",tree);
            tree.insert(k, v)
        }
        tree.check_integrity();
        tree.balance_weight();
        tree

    }

    pub fn empty() -> WeightBalancedSearchTree<K,V> {
        WeightBalancedSearchTree{
            root:None,
            arena:vec![],
            indecies: vec![],
        }
    }

    pub fn insert(&mut self,k:K,v:V) {
        let path = self.key_path(&k);
        // eprintln!("KP:{:?}",path);
        self.add_path(&path,k);
        let new_index = self.arena.len();
        self.arena.push(STNode::new(k,v));
        self.indecies.push(new_index);
        if let Some(&(Some(b),i)) = path.first() {
            if b {
                self.arena[i].right = Some(new_index);
                self.arena[new_index].parent = Some((true,i));
            }
            else {
                self.arena[i].left = Some(new_index);
                self.arena[new_index].parent = Some((false,i));
            }
        }
        else {
            self.root = Some(new_index)
        }
    }

    pub fn insert_value_at(&mut self,k:K,v:V,index:usize) {
        let path = self.key_path_at(Some(index),&k,self.depth(Some(index)));
        // eprintln!("KP:{:?}",path);
        self.add_path(&path,k);
        let new_index = self.arena.len();
        self.arena.push(STNode::new(k,v));
        self.indecies.push(new_index);
        if let Some(&(Some(b),i)) = path.first() {
            if b {
                self.arena[i].right = Some(new_index);
                self.arena[new_index].parent = Some((true,i));
            }
            else {
                self.arena[i].left = Some(new_index);
                self.arena[new_index].parent = Some((false,i));
            }
        }
        else {
            self.root = Some(new_index)
        }
    }

    pub fn reinsert_node(&mut self, node:usize) {
        self.reinsert_node_at(node,None);
    }

    pub fn reinsert_node_at(&mut self,node:usize,insert_index:Option<usize>) {
        let STNode{key:k,..} = self.arena[node];
        let node_sum = self.node_sum(Some(node));
        let path = self.key_path_at(insert_index,&k,self.depth(insert_index));
        // eprintln!("KP:{:?}",path);
        self.add_path(&path,node_sum);
        if let Some(&(Some(b),i)) = path.first() {
            if b {
                self.arena[i].right = Some(node);
                self.arena[node].parent = Some((true,i));
            }
            else {
                self.arena[i].left = Some(node);
                self.arena[node].parent = Some((false,i));
            }
        }
        else {
            self.root = Some(node);
            self.arena[node].parent = None;
        }
    }

    pub fn unchecked_switch(&mut self,a:usize,b:usize) {
        //
        // eprintln!("a:{:?}",self.arena[a]);
        // eprintln!("b:{:?}",self.arena[b]);

        // let ap = self.arena[a].parent;
        // let bp = self.arena[b].parent;
        // let al = self.arena[a].left;
        // let ar = self.arena[a].right;
        // let bl = self.arena[b].left;
        // let br = self.arena[b].right;
        //
        // self.unlink(a);
        // self.unlink(b);
        //
        // self.link(ap,Some(b));
        // self.link(bp,Some(a));
        //
        // self.link(Some((false,b)),al);
        // self.link(Some((true,b)),ar);
        //
        // self.link(Some((false,a)),bl);
        // self.link(Some((true,a)),br);
        //
        // self.arena.swap(a,b);
        // self.indecies.swap(a,b);
        //
        // self.establish_node_sums(a);
        // self.establish_node_sums(b);
        //
        // if let Some((_,api)) = ap {
        //     self.establish_node_sums(api);
        // }
        // if let Some((_,bpi)) = bp {
        //     self.establish_node_sums(bpi);
        // }
        //
        // eprintln!("a:{:?}",self.arena[a]);
        // eprintln!("b:{:?}",self.arena[b]);

        let apo = self.arena[a].parent;
        let bpo = self.arena[b].parent;
        let alo = self.arena[a].left;
        let aro = self.arena[a].right;
        let blo = self.arena[b].left;
        let bro = self.arena[b].right;

        if let Some(ap) = apo {
            if ap.0 {
                self.arena[ap.1].right = Some(b);
            }
            else {
                self.arena[ap.1].left = Some(b);
            }
        }
        else {
            self.root = Some(b);
        }
        //
        // eprintln!("a:{:?}",self.arena[a]);
        // eprintln!("b:{:?}",self.arena[b]);

        if let Some(a_left) = alo {
            self.arena[a_left].parent = Some((false,b));
        }
        if let Some(a_right) = aro {
            self.arena[a_right].parent = Some((true,b));
        }
        if let Some(b_left) = blo {
            self.arena[b_left].parent = Some((false,a));
        }
        if let Some(b_right) = bro {
            self.arena[b_right].parent = Some((true,a));
        }
        //
        // eprintln!("a:{:?}",self.arena[a]);
        // eprintln!("b:{:?}",self.arena[b]);

        if let Some(bp) = bpo {
            if bp.0 {
                self.arena[bp.1].right = Some(a);
            }
            else {
                self.arena[bp.1].left = Some(a)
            }
        }
        else {
            self.root = Some(a)
        }
        // eprintln!("a:{:?}",self.arena[a]);
        // eprintln!("b:{:?}",self.arena[b]);

        self.arena.swap(a,b);
        self.indecies.swap(a,b);

        // eprintln!("a:{:?}",self.arena[a]);
        // eprintln!("b:{:?}",self.arena[b]);
    }


    pub fn send_to_back(&mut self,index:usize) -> usize {
        // eprintln!("Sending");
        let last = self.arena.len().checked_sub(1).unwrap();
        self.unchecked_switch(index, last);
        // eprintln!("Switched");
        // eprintln!("{:?}",self);
        last
    }

    pub fn index_path(&self,mut index:usize) -> Vec<(Option<bool>,usize)> {
        let depth = self.depth(Some(index));
        let mut path = Vec::with_capacity(depth);
        let mut current = (None,index);
        path.push(current);
        while let Some(parent) = self.arena[current.1].parent {
            current = (Some(parent.0),parent.1);
            path.push(current);
        }
        path
    }

    pub fn unlink_back(&mut self) -> Vec<usize> {
        let last = self.arena.len() - 1;
        self.unlink(last);
        self.children(last)
    }

    pub fn key_path(&self,k:&K) -> Vec<(Option<bool>,usize)> {
        self.key_path_at(self.root,k,0)
    }

    pub fn key_path_at(&self,index_opt:Option<usize>, k:&K, depth: usize) -> Vec<(Option<bool>,usize)> {
        // eprintln!("Path");
        // eprintln!("{:?}",k);
        if let Some(index) = index_opt {
            let STNode{key,left,right,..} = &self.arena[index];
            // eprintln!("{:?}",key);
            // eprintln!("{:?}",self.arena[index]);
            let path = if k < key {
                let mut path = self.key_path_at(*left, k, depth + 1);
                path.push((Some(false),index));
                path
            }
            else {
                let mut path = self.key_path_at(*right, k, depth + 1);
                path.push((Some(true),index));
                path
            };
            // eprintln!("PP:{:?}",path);
            return path
        }
        else {
            return Vec::with_capacity(depth);
        }
    }

    pub fn add_path(&mut self,path:&Vec<(Option<bool>,usize)>, k:K) {
        for (b,i) in path.iter().filter_map(|(b_opt,i)| if let Some(b) = b_opt {Some((*b,*i))} else {None}) {
            if b {
                self.arena[i].right_sum += k;
            }
            else {
                self.arena[i].left_sum += k;
            }
        }
    }

    pub fn subtract_path(&mut self,path:&Vec<(Option<bool>,usize)>, k:K) {
        for (b,i) in path.iter().filter_map(|(b_opt,i)| if let Some(b) = b_opt {Some((*b,*i))} else {None}) {
            if b {
                self.arena[i].right_sum -= k;
            }
            else {
                self.arena[i].left_sum -= k;
            }
        }
    }

    pub fn unlink(&mut self,index:usize) {
        if let Some((pb,pi)) = self.arena[index].parent {
            if pb {
                self.arena[pi].right = None;
                self.establish_node_sums(pi);
            }
            else {
                self.arena[pi].left = None;
                self.establish_node_sums(pi);
            }
        }
        self.arena[index].parent = None;
    }

    pub fn link(&mut self, parent:Option<(bool,usize)>,child:Option<usize>) {
        // eprintln!("Linking:{:?},{:?}",parent,child);
        if let Some((pb,pi)) = parent {
            if pb {
                self.arena[pi].right = child;
            }
            else {
                self.arena[pi].left = child;
            }
            self.establish_node_sums(pi);
            // eprintln!("Linked:{:?}",self.arena[pi]);
        }
        else {
            self.root = child;
        }
        if let Some(ci) = child {
            self.arena[ci].parent = parent;
            // eprintln!("Linked:{:?}",self.arena[ci]);
        }
    }

    pub fn new_root(&mut self,k:K,v:V) {
        self.root = Some(self.arena.len());
        let new_node = STNode::new(k,v);
        self.arena.push(new_node);
    }

    pub fn unchecked_rotate_right(&mut self,index:usize) {

        // eprintln!("Rotating right: {:?}",index);

        let STNode{key:index_key,left:index_left,right:index_right,parent:index_parent,..} = self.arena[index];
        let pivot = index_left.unwrap();
        let pivot_right = self.arena[pivot].right;
        let pivot_left = self.arena[pivot].left;

        // eprintln!("I{:?}:{:?}",index,self.arena[index]);
        // eprintln!("P{:?}:{:?}",pivot,self.arena[pivot]);


        self.unlink(index);
        self.unlink(pivot);
        if let Some(pli) = pivot_left {
            self.unlink(pli);
        }
        if let Some(pri) = pivot_right {
            self.unlink(pri);
        }

        self.arena.swap(index,pivot);
        self.indecies.swap(index,pivot);

        self.link(Some((false,pivot)),pivot_right);
        self.link(Some((true,pivot)),index_right);
        self.link(Some((false,index)),pivot_left);
        self.link(Some((true,index)),Some(pivot));
        self.link(index_parent,Some(index));


        // eprintln!("I{:?}:{:?}",index,self.arena[index]);
        // eprintln!("P{:?}:{:?}",pivot,self.arena[pivot]);

        //
        // self.arena.swap(index,pivot);
        // self.indecies.swap(index,pivot);
        //
        // self.arena[pivot].parent = Some((true,index));
        // self.arena[pivot].left = baton;
        // self.arena[pivot].left_sum = self.node_sum(baton);
        //
        // self.arena[index].parent = index_parent;
        // self.arena[index].right = Some(pivot);
        // self.arena[index].right_sum = self.node_sum(Some(pivot));
        //
        // if let Some(bi) = baton {
        //     self.arena[bi].parent = Some((false,pivot))
        // }
        // if let Some(iri) = index_right {
        //     self.arena[iri].parent = Some((true,pivot))
        // }
        // if let Some(pli) = self.arena[pivot].left {
        //     self.arena[pli].parent = Some((false,index))
        // }

        //
        // let pivot: usize = self.arena[index].left.unwrap();
        //
        // eprintln!("I:{:?}",self.arena[index]);
        // eprintln!("P:{:?}",self.arena[pivot]);
        //
        // self.arena[pivot].parent = self.arena[index].parent;
        // let baton = self.arena[pivot].right;
        // self.arena[pivot].right = Some(index);
        //
        // self.arena[index].parent = Some((true,pivot));
        // self.arena[index].left = baton;
        //
        // self.arena[index].left_sum = self.node_sum(baton);
        // self.arena[pivot].right_sum = self.node_sum(Some(index));
        //
        // if let Some(bi) = baton {
        //     self.arena[bi].parent = Some((false,index));
        // }
        // if let Some(parent) = self.arena[pivot].parent {
        //     if parent.0 {
        //         self.arena[parent.1].right = Some(pivot);
        //         self.arena[parent.1].right_sum = self.node_sum(Some(pivot));
        //     }
        //     else {
        //         self.arena[parent.1].left = Some(pivot);
        //         self.arena[parent.1].left_sum = self.node_sum(Some(pivot));
        //     }
        // }
        // else {
        //     self.root = pivot
        // }
        //
        //
        // eprintln!("I:{:?}",self.arena[index]);
        // eprintln!("P:{:?}",self.arena[pivot]);
        // if let Some(bi) = baton {
            // eprintln!("B:{:?}",self.arena[bi]);
        // }
    }

    pub fn unchecked_rotate_left(&mut self,index:usize) {
        // eprintln!("Rotating left: {:?}",index);

        let STNode{key:index_key,left:index_left,right:index_right,parent:index_parent,..} = self.arena[index];
        let pivot = index_right.unwrap();
        let pivot_left = self.arena[pivot].left;
        let pivot_right = self.arena[pivot].right;

        // eprintln!("I{:?}:{:?}",index,self.arena[index]);
        // eprintln!("P{:?}:{:?}",pivot,self.arena[pivot]);

        self.unlink(index);
        self.unlink(pivot);
        if let Some(pli) = pivot_left {
            self.unlink(pli);
        }
        if let Some(pri) = pivot_right {
            self.unlink(pri)
        }

        self.arena.swap(index,pivot);
        self.indecies.swap(index,pivot);

        self.link(Some((false,pivot)),index_left);
        self.link(Some((true,pivot)),pivot_left);
        self.link(Some((true,index)),pivot_right);
        self.link(Some((false,index)),Some(pivot));
        self.link(index_parent,Some(index));

        // eprintln!("I{:?}:{:?}",index,self.arena[index]);
        // eprintln!("P{:?}:{:?}",pivot,self.arena[pivot]);

        //
        // self.arena.swap(index,pivot);
        // self.indecies.swap(index,pivot);
        //
        // self.arena[pivot].parent = Some((false,index));
        // self.arena[pivot].right = baton;
        // self.arena[pivot].right_sum = self.node_sum(baton);
        //
        // self.arena[index].parent = index_parent;
        // self.arena[index].left = Some(pivot);
        // self.arena[index].left_sum = self.node_sum(Some(pivot));
        //
        // if let Some(bi) = baton {
        //     self.arena[bi].parent = Some((true,pivot))
        // }
        // if let Some(ili) = index_left {
        //     self.arena[ili].parent = Some((false,pivot))
        // }
        // if let Some(pri) = self.arena[pivot].right {
        //     self.arena[pri].parent = Some((true,index))
        // }

        // eprintln!("Rotating left: {:?}",index);
        //
        // let pivot: usize = self.arena[index].right.unwrap();
        //
        // eprintln!("I:{:?}",self.arena[index]);
        // eprintln!("P:{:?}",self.arena[pivot]);

        // self.arena[pivot].parent = self.arena[index].parent;
        // let baton = self.arena[pivot].left;
        // self.arena[pivot].left = Some(index);
        //
        // self.arena[index].parent = Some((false,pivot));
        // self.arena[index].right = baton;
        //
        // self.arena[index].right_sum = self.node_sum(baton);
        // self.arena[pivot].left_sum = self.node_sum(Some(index));
        //
        // if let Some(bi) = baton {
        //     self.arena[bi].parent = Some((true,index));
        // }
        //
        // if let Some(parent) = self.arena[pivot].parent {
        //     if parent.0 {
        //         self.arena[parent.1].right = Some(pivot);
        //         self.arena[parent.1].right_sum = self.node_sum(Some(pivot));
        //     }
        //     else {
        //         self.arena[parent.1].left = Some(pivot);
        //         self.arena[parent.1].left_sum = self.node_sum(Some(pivot));
        //     }
        // }
        // else {
        //     self.root = pivot
        // }

        // eprintln!("I:{:?}",self.arena[index]);
        // eprintln!("P:{:?}",self.arena[pivot]);
        // if let Some(bi) = baton {
            // eprintln!("B:{:?}",self.arena[bi]);
        // }
        // panic!();

    }

    pub fn node_sum(&self,index:Option<usize>) -> K {
        let mut sum = zero();
        if let Some(&STNode{key,left,right,left_sum,right_sum,..}) = index.map(|x| &self.arena[x]) {
            sum += key;
            if left.is_some() {
                sum += left_sum;
            }
            if right.is_some() {
                sum += right_sum;
            }
        }
        sum
    }

    pub fn node_lkr(&self,index:Option<usize>) -> (K,K,K) {
        let mut sum = (zero(),zero(),zero());
        if let Some(&STNode{key,left_sum,right_sum,..}) = index.map(|x| &self.arena[x]) {
            sum = (left_sum,key,right_sum);
        }
        sum
    }

    pub fn rightmost(&self,index:usize) -> usize {
        if let Some(STNode{right:Some(right),..}) = self.arena.get(index) {
            self.rightmost(*right)
        }
        else {index}
    }

    pub fn leftmost(&self,index:usize) -> usize {
        if let Some(STNode{left:Some(left),..}) = self.arena.get(index) {
            self.leftmost(*left)
        }
        else {index}
    }

    pub fn tilt(&self, index: usize) -> K {
        self.arena[index].right_sum - self.arena[index].left_sum
    }

    pub fn balance_weight(&mut self) {
        let root = self.root;
        // eprintln!("{:?}",self);
        // self.check_integrity();
        self.balance_weight_recursive(root);
    }

    pub fn balance_weight_recursive(&mut self, index_option:Option<usize>) {
        if let Some(index) = index_option {
            // eprintln!("Recursively balancing:{:?}",index);
            // eprintln!("{:?}",self.arena[index]);
            let STNode{left,right,..} = self.arena[index];
            self.balance_weight_recursive(left);
            self.balance_weight_recursive(right);
            self.balance_weight_node(index)
        }
    }

    pub fn check_tilt(&self,index:usize) -> (K,K) {
        let STNode{key,right,left,..} = self.arena[index];

        let (rl,rk,rr) = self.node_lkr(right);
        let (ll,lk,lr) = self.node_lkr(left);
        //
        // eprintln!("{:?}",self);
        // eprintln!("{:?}",self.arena[index]);
        // eprintln!("{:?}",(ll,lk,lr));
        // eprintln!("{:?}",key);
        // eprintln!("{:?}",(rl,rk,rr));

        let left_shift_tilt = rr - (ll + lk + lr + rl + key);
        let right_shift_tilt = (rr + rl + rk + key + lr) - ll;

        // eprintln!("{:?},{:?}",left_shift_tilt,right_shift_tilt);

        (left_shift_tilt.abs(),right_shift_tilt.abs())

    }

    pub fn balance_weight_node(&mut self, index:usize) {
        // eprintln!("Balancing {:?}",index);
        let mut counter = 0;
        loop {
            counter += 1;
            // self.check_integrity();
            if counter > 5 {
                // eprintln!("{:?}",self);
                panic!("Something went pretty wrong, I think! Balancing node for more than 1000 cycles")
            }
            let tilt = self.tilt(index).abs();
            let (left_shift_tilt,right_shift_tilt) = self.check_tilt(index);
            // eprintln!("{:?},{:?},{:?}",left_shift_tilt,tilt,right_shift_tilt);
            if (left_shift_tilt < tilt) || (right_shift_tilt < tilt) {
                if left_shift_tilt < right_shift_tilt {
                    // eprintln!("Rotating left");
                    self.unchecked_rotate_left(index);
                }
                else {
                    // eprintln!("Rotating right");
                    self.unchecked_rotate_right(index);
                }
            }
            else {
                break
            }
            // eprintln!("{:?}",self.tilt(index));
            // self.check_integrity();
            // if tilt.abs() > (left_shift_tilt,right_shift_tilt).iter().min() {
            //     if tilt > zero() {
                    eprintln!("Rotating left");
            //         self.unchecked_rotate_left(index)
            //     }
            //     else if tilt <= zero() {
                    eprintln!("Rotating right");
            //         self.unchecked_rotate_right(index)
            //     }
            // }

        }
    }

    pub fn sum(&self) -> K {
        self.node_sum(self.root)
    }

    pub fn children(&self,index:usize) -> Vec<usize> {
        self.arena[index].children()
    }

    pub fn depth(&self, mut index_pass:Option<usize>) -> usize {
        if let Some(mut index) = index_pass {
            let mut counter = 0;
            while let Some(parent) = self.arena[index].parent {
                counter += 1;
                index = parent.1;
            }
            counter
        }
        else {0}
    }

    // pub fn descent_path(&self,k:K) -> usize {
    //     let mut current = 0;
    //     let mut cumulative_sum = zero();
    //     assert!(self.sum() > zero());
    //     while let Some(&STNode{key,left,right,left_sum,right_sum,..}) = self.arena.get(current) {
    //         if k <= cumulative_sum + left_sum {
    //             if let Some(left_index) = left {
    //                 current = left_index;
    //             }
    //             else {
    //                 break
    //             }
    //         }
    //         cumulative_sum += left_sum;
    //         if k <= cumulative_sum {
    //             break
    //         }
    //         cumulative_sum += key;
    //         if let Some(right_index) = right {
    //             current = right_index
    //         }
    //         else {
    //             break
    //         }
    //
    //     }
    //     current
    // }

    pub fn sample_path(&self,k:K) -> Vec<(Option<bool>,usize)> {
        self.sample_path_from(k, self.root, zero(), 0)
    }

    pub fn sample_path_from(&self,k:K,index_opt:Option<usize>,cumulative:K,depth:usize) -> Vec<(Option<bool>,usize)> {
        if let Some(i) = index_opt {
            let STNode{key,left,right,left_sum,right_sum,..} = self.arena[i];
            let path: Vec<(Option<bool>,usize)> = {
                 if k <= cumulative + left_sum {
                     let mut path = self.sample_path_from(k,self.arena[i].left,cumulative, depth + 1);
                     path.push((Some(false),i));
                     path
                }
                else if k > (cumulative + left_sum + key) {
                    let mut path = Vec::with_capacity(depth);
                    path.push((None,i));
                    path
                }
                else {
                    let mut path = self.sample_path_from(k,self.arena[i].right,cumulative, depth+1);
                    path.push((Some(true),i));
                    path
                }

            };
            path
        }
        else {Vec::with_capacity(depth)}
    }

    pub fn descend_index(&self,k:K) -> usize {
        let mut current = self.root.unwrap();
        let mut next = self.root;
        let mut cumulative: K = zero();
        let mut counter = 0;
        while let Some(index) = next {
            counter += 1;
            if counter > 10000 {
                panic!("Probably a cycle, descending for more than 10000 steps");
            }
            let STNode{key,left,right,left_sum,right_sum,..} = self.arena[index];
            let current = index;
            if k <= cumulative + left_sum {
                 next = left
            }
            else if k > (cumulative + left_sum + key) {
                cumulative += left_sum + key;
                next = right
            }
            else {
                break
            }
        }
        current
    }


    pub fn remove(&mut self,index:usize) -> Option<(K,V)> {
        // self.check_integrity();
        // eprintln!("{:?}",self);
        // eprintln!("#############################");
        // eprintln!("#############################");
        // eprintln!("Removing {:?}",index);
        // eprintln!("#############################");
        // eprintln!("#############################");
        // eprintln!("{:?}",self.arena[index]);

        // let last = self.send_to_back(index);
        // self.check_integrity();

        let path = self.index_path(index);
        let STNode{parent,key,value,left_sum,right_sum,..} = self.arena[index];
        let mut children = self.children(index);
        // eprintln!("{:?}",children);
        for &child in &children {
            self.unlink(child);
        }
        // self.subtract_path(&path, key + left_sum + right_sum);
        self.subtract_path(&path, key);
        self.unlink(index);

        // let parent = self.arena[last].parent;
        // eprintln!("Unlinked");
        // eprintln!("{:?}",self);
        // eprintln!("Reinserting");
        // let mut children = self.unlink_back();
        // eprintln!("Switch Remove");
        // eprintln!("{:?}",self);
        if let Some((pb,pi)) = parent {
            // eprintln!("Reinserting with parents");
            // eprintln!("{:?}",children);
            self.establish_node_sums(pi);
            for child in children {
                self.reinsert_node_at(child, Some(pi))
            }
        }
        else {
            // eprintln!("Reinserting at root");
            for i in 0..children.len() {
                self.reinsert_node_at(children[i], children.get(i+1).map(|x| *x));
            }
        }

        // eprintln!("Inserted children");
        // eprintln!("{:?}",self);
        //
        // let value = self.arena.pop().unwrap().value;
        // self.indecies.pop();

        // self.check_integrity();

        // eprintln!("Attempting to balance");
        // eprintln!("{:?}",self);
        if self.arena.len() > 0 {
            self.balance_weight();
        }
        // eprintln!("{:?}",self);
        Some((key,value))
    }

    pub fn draw(&mut self) -> Option<(K,V)> {
        // self.check_integrity();
        let draw: f64 = <f64 as NumCast>::from(self.sum()).unwrap() * random::<f64>();
        self.draw_specified(K::from(draw).unwrap())
    }

    pub fn establish_sums(&mut self) {
        if let Some(root) = self.root {
            self.establish_node_sums_recursively(root);
        }
    }

    pub fn establish_node_sums_recursively(&mut self,index:usize) {
        for child in self.children(index) {
            self.establish_node_sums_recursively(child);
        }
        self.establish_node_sums(index);
    }

    pub fn establish_node_sums(&mut self,index:usize) {
        self.arena[index].left_sum = self.node_sum(self.arena[index].left);
        self.arena[index].right_sum = self.node_sum(self.arena[index].right);
    }

    pub fn draw_specified(&mut self,draw:K) -> Option<(K,V)> {
        let path = self.sample_path(draw);
        self.remove(path.first().map(|x| x.1).unwrap())
    }

    pub fn draw_replace(&mut self) -> Option<(K,V)> {
        let draw: f64 = <f64 as NumCast>::from(self.sum()).unwrap() * random::<f64>();
        self.draw_replace_specified(K::from(draw).unwrap())
    }

    pub fn draw_replace_specified(&mut self,draw:K) -> Option<(K,V)> {
        let index = self.descend_index(draw);
        self.arena.get(index).map(|STNode{key,value,..}| (*key,*value))
    }

    pub fn check_integrity(&self) {
        if !self.check_weights_recursive(self.root,0) {
            // eprintln!("{:?}",self);
            panic!("Invalid weights");
        }
        for i in self.rooted_nodes(self.root) {
            let path_up = self.index_path(i);
            if path_up.last().map(|x| x.1) != self.root {
                // eprintln!("{:?}",self);
                // eprintln!("{:?}",self.rooted_nodes(self.root));
                // eprintln!("{:?}",self.arena[i]);
                // eprintln!("{:?}",path_up);
                // eprintln!("{:?}",i);
                panic!("Invalid parents");
            }
        //     let sum_position: K = path_up.iter().map(|&(b_opt,i)|
        //         {
        //             if let Some(b) = b_opt
        //                 {
        //                     if b {
        //                         self.arena[i].left_sum + self.arena[i].key
        //                     }
        //                     else {zero()}
        //                 }
        //             else {self.arena[i].left_sum + self.arena[i].key}
        //         })
        //         .fold(zero(),|mut acc,x| {acc += x; acc});
        //
        //     let path_down = self.sample_path(sum_position);
        //     if path_up.iter().rev().zip(path_down.iter().rev()).any(|(up,down)| up.1 != down.1) {
        //         // eprintln!("{:?}",self);
        //         // eprintln!("{:?}",path_up);
        //         // eprintln!("{:?}",path_down);
        //         // eprintln!("{:?}",sum_position);
        //         // eprintln!("{:?}",i);
        //         panic!("Invalid path");
        //     }
        }
    }

    pub fn check_weights_recursive(&self,index_opt:Option<usize>,counter:usize) -> bool {
        if counter > 1000 {
            // eprintln!("{:?}",self);
            // eprintln!("Current:{:?}",index_opt);
            panic!("Cycle detected, 1000 recursions through tree checking weight");
        }
        let mut valid = true;
        let mut error = (zero(),zero());
        if let Some(index) = index_opt {
            if !self.check_weights_recursive(self.arena[index].left, counter + 1) {
                valid = false;
            }
            if !self.check_weights_recursive(self.arena[index].right, counter + 1) {
                valid = false;
            }
            if (self.node_sum(self.arena[index].left) - self.arena[index].left_sum) > <K as NumCast>::from(0.0001).unwrap() {
                valid = false;
                error = (self.node_sum(self.arena[index].left),self.arena[index].left_sum)
            }
            if (self.node_sum(self.arena[index].right) - self.arena[index].right_sum) > <K as NumCast>::from(0.0001).unwrap() {
                valid = false;
                error = (self.node_sum(self.arena[index].right),self.arena[index].right_sum)
            }
        }
        if !valid {
            // eprintln!("{:?}",self);
            // eprintln!("{:?}",index_opt);
            // eprintln!("{:?}",error);
            panic!("Invalid weights");
        }
        valid
    }

    pub fn rooted_nodes(&self,index_opt:Option<usize>) -> Vec<usize> {
        let mut rooted_nodes = vec![];
        if let Some(index) = index_opt {
            rooted_nodes.append(&mut self.rooted_nodes(self.arena[index].left));
            rooted_nodes.append(&mut self.rooted_nodes(self.arena[index].right));
            rooted_nodes.push(index);
        }
        rooted_nodes
    }

}



#[cfg(test)]
mod tests {

    use super::*;
    use rand::{thread_rng,Rng};

    trait ValidKey: PartialOrd + Sub<Self,Output=Self> + Add<Self,Output=Self> + AddAssign<Self> + SubAssign<Self> + NumCast + ToPrimitive + Zero + Signed + Copy + Debug {}

    impl ValidKey for f64 {}
    impl ValidKey for i32 {}

    pub fn test_vec_f64() -> Vec<f64> {
        vec![10.,3.,4.,1.,0.,1.,0.5]
    }

    pub fn test_vec_usize() -> Vec<usize> {
        vec![5,3,7,4,10,0,0,0,1]
    }

    pub fn test_vec_repetitive() -> Vec<i32> {
        vec![1,1,1,1,1,1,1,1]
    }

    pub fn test_vec_empty() -> Vec<i32> {
        vec![]
    }

    pub fn test_vec_zero() -> Vec<i32> {
        vec![0,0,0,0,0,0]
    }

    pub fn test_vec_small_random_f64() -> Vec<f64> {
        let mut rng = thread_rng();
        (0..10).map(|_| rng.gen::<f64>()).collect()
    }

    pub fn test_vec_medium_random_f64() -> Vec<f64> {
        let mut rng = thread_rng();
        (0..100).map(|_| rng.gen::<f64>()).collect()
    }

    pub fn test_vec_large_random_f64() -> Vec<f64> {
        let mut rng = thread_rng();
        (0..10000).map(|_| rng.gen::<f64>()).collect()
    }

    pub fn test_vec_large_random_i32() -> Vec<i32> {
        let mut rng = thread_rng();
        (0..10000).map(|_| rng.gen_range::<i32,i32,i32>(0,1000)).collect()
    }

    pub fn test_vec_small_random_i32() -> Vec<i32> {
        let mut rng = thread_rng();
        (0..10).map(|_| rng.gen_range::<i32,i32,i32>(0,1000)).collect()
    }

    fn test_vec<K: ValidKey>(test_vec:Vec<K>)
    where
        Standard: Distribution<K>
    {
        let mut tree = WeightBalancedSearchTree::<K,usize>::index_tree(test_vec.clone());

        for _ in test_vec {
            // eprintln!("{:?}",tree.draw());
        }
    }

    fn test_vec_replacement<K: ValidKey>(test_vec:Vec<K>)
    where
        Standard: Distribution<K>
    {
        let mut tree = WeightBalancedSearchTree::<K,usize>::index_tree(test_vec.clone());

        for _ in test_vec {
            // eprintln!("{:?}",tree.draw_replace());
        }
    }

    #[test]
    pub fn microtest() {
        let a = vec![1.,2.,3.];
        test_vec(a);
    }

    #[test]
    pub fn minitest() {
        let a = vec![1.,2.,3.,4.];
        test_vec(a);
    }

    #[test]
    pub fn test_f64() {
        let a = test_vec_f64();
        test_vec(a);
    }
    // #[test]
    // pub fn replacement_test_f64() {
    //     let a = test_vec_f64();
    //     test_vec_replacement(a);
    // }

    #[test]
    pub fn test_repetitive() {
        let c = test_vec_repetitive();
        test_vec(c);
    }
    #[test]
    pub fn replacement_test_repetitive() {
        let c = test_vec_repetitive();
        test_vec_replacement(c);
    }

    #[test]
    pub fn test_empty() {
        let d = test_vec_empty();
        test_vec(d);
    }
    #[test]
    pub fn replacement_test_empty() {
        let d = test_vec_empty();
        test_vec_replacement(d);
    }

    #[test]
    pub fn test_zeros() {
        let e = test_vec_zero();
        test_vec(e);
    }
    #[test]
    pub fn replacement_test_zeros() {
        let e = test_vec_zero();
        test_vec_replacement(e);
    }

    #[test]
    pub fn test_small_random_f64() {
        let f = test_vec_small_random_f64();
        test_vec(f);
    }
    #[test]
    pub fn replacement_test_small_random_f64() {
        let f = test_vec_small_random_f64();
        test_vec_replacement(f);
    }

    #[test]
    pub fn test_medium_random_f64() {
        let g = test_vec_medium_random_f64();
        test_vec(g);
    }
    #[test]
    pub fn replacement_test_medium_random_f64() {
        let g = test_vec_medium_random_f64();
        test_vec_replacement(g);
    }

    #[test]
    pub fn test_large_random_f64() {
        let h = test_vec_large_random_f64();
        test_vec(h);
    }
    #[test]
    pub fn replacement_test_large_random_f64() {
        let h = test_vec_large_random_f64();
        test_vec_replacement(h);
    }

    #[test]
    pub fn test_small_random_i32() {
        let i = test_vec_small_random_i32();
        test_vec(i);
    }

    #[test]
    pub fn test_large_random_i32() {
        let i = test_vec_large_random_i32();
        test_vec(i);
    }
    #[test]

    pub fn replacement_test_large_random_i32() {
        let i = test_vec_large_random_i32();
        test_vec_replacement(i);
    }



}
