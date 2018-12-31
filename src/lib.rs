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
    root: usize,
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
        tree
    }

    pub fn empty() -> WeightBalancedSearchTree<K,V> {
        WeightBalancedSearchTree{
            root:0,
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
            self.root = node;
            self.arena[node].parent = None;
        }
    }

    pub fn unchecked_switch(&mut self,a:usize,b:usize) {
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
            self.root = b;
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
            self.root = a
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
        self.key_path_at(if self.arena.len() > 0 {Some(self.root)} else {None},k,0)
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
        if let Some(parent) = self.arena[index].parent {
            if parent.0 {
                self.arena[parent.1].right = None;
            }
            else {
                self.arena[parent.1].left = None;
            }
        }
    }

    pub fn new_root(&mut self,k:K,v:V) {
        assert!(self.arena.len() < 1);
        assert!(self.root == 0);
        let new_node = STNode::new(k,v);
        self.arena.push(new_node);
    }

    pub fn unchecked_rotate_right(&mut self,index:usize) {
        // eprintln!("Rotating right: {:?}",index);

        let pivot: usize = self.arena[index].left.unwrap();

        // eprintln!("I:{:?}",self.arena[index]);
        // eprintln!("P:{:?}",self.arena[pivot]);

        self.arena[pivot].parent = self.arena[index].parent;
        let baton = self.arena[pivot].right;
        self.arena[pivot].right = Some(index);

        self.arena[index].parent = Some((true,pivot));
        self.arena[index].left = baton;

        self.arena[index].left_sum = self.node_sum(baton);
        self.arena[pivot].right_sum = self.node_sum(Some(index));

        if let Some(bi) = baton {
            self.arena[bi].parent = Some((false,index));
        }
        if let Some(parent) = self.arena[pivot].parent {
            if parent.0 {
                self.arena[parent.1].right = Some(pivot);
                self.arena[parent.1].right_sum = self.node_sum(Some(pivot));
            }
            else {
                self.arena[parent.1].left = Some(pivot);
                self.arena[parent.1].left_sum = self.node_sum(Some(pivot));
            }
        }
        else {
            self.root = pivot
        }


        // eprintln!("I:{:?}",self.arena[index]);
        // eprintln!("P:{:?}",self.arena[pivot]);
        // if let Some(bi) = baton {
            // eprintln!("B:{:?}",self.arena[bi]);
        // }
    }

    pub fn unchecked_rotate_left(&mut self,index:usize) {

        // eprintln!("Rotating left: {:?}",index);

        let pivot: usize = self.arena[index].right.unwrap();

        // eprintln!("I:{:?}",self.arena[index]);
        // eprintln!("P:{:?}",self.arena[pivot]);

        self.arena[pivot].parent = self.arena[index].parent;
        let baton = self.arena[pivot].left;
        self.arena[pivot].left = Some(index);

        self.arena[index].parent = Some((false,pivot));
        self.arena[index].right = baton;

        self.arena[index].right_sum = self.node_sum(baton);
        self.arena[pivot].left_sum = self.node_sum(Some(index));

        if let Some(bi) = baton {
            self.arena[bi].parent = Some((true,index));
        }

        if let Some(parent) = self.arena[pivot].parent {
            if parent.0 {
                self.arena[parent.1].right = Some(pivot);
                self.arena[parent.1].right_sum = self.node_sum(Some(pivot));
            }
            else {
                self.arena[parent.1].left = Some(pivot);
                self.arena[parent.1].left_sum = self.node_sum(Some(pivot));
            }
        }
        else {
            self.root = pivot
        }

        // eprintln!("I:{:?}",self.arena[index]);
        // eprintln!("P:{:?}",self.arena[pivot]);
        // if let Some(bi) = baton {
            // eprintln!("B:{:?}",self.arena[bi]);
        // }
        // panic!();

    }

    pub fn node_sum(&self,index:Option<usize>) -> K {
        let mut sum = zero();
        if let Some(&STNode{key,left_sum,right_sum,..}) = index.map(|x| &self.arena[x]) {
            sum += key + left_sum + right_sum;
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
        self.balance_weight_recursive(Some(root));
    }

    pub fn balance_weight_recursive(&mut self, index_option:Option<usize>) {
        if let Some(index) = index_option {
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
        // eprintln!("{:?}",(ll,lk,lr));
        // eprintln!("{:?}",key);
        // eprintln!("{:?}",(rl,rk,rr));

        let left_shift_tilt = rr - (ll + lk + ll + rl + key);
        let right_shift_tilt = (rr + rl + rk + key + lr) - ll;

        (left_shift_tilt.abs(),right_shift_tilt.abs())

    }

    pub fn balance_weight_node(&mut self, index:usize) {
        // eprintln!("Balancing {:?}",index);
        let mut counter = 0;
        loop {
            if counter > 1000 {
                panic!("Something went pretty wrong, I think! Balancing node for more than 1000 cycles")
            }
            counter += 1;
            let tilt = self.tilt(index).abs();
            let (left_shift_tilt,right_shift_tilt) = self.check_tilt(index);
            // eprintln!("{:?},{:?},{:?}",left_shift_tilt,tilt,right_shift_tilt);
            if (left_shift_tilt < tilt) || (right_shift_tilt < tilt) {
                if left_shift_tilt < right_shift_tilt {
                    // eprintln!("Rotating left");
                    self.unchecked_rotate_left(index);
                }
                else {
                    self.unchecked_rotate_right(index);
                }
            }
            else {
                break
            }
            // if tilt.abs() > (left_shift_tilt,right_shift_tilt).iter().min() {
            //     if tilt > zero() {
            //         eprintln!("Rotating left");
            //         self.unchecked_rotate_left(index)
            //     }
            //     else if tilt <= zero() {
            //         eprintln!("Rotating right");
            //         self.unchecked_rotate_right(index)
            //     }
            // }

        }
    }

    pub fn sum(&self) -> K {
        self.node_sum(Some(self.root))
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

    pub fn sample_path_from(&self,k:K,i:usize,cumulative:K,depth:usize) -> Vec<(Option<bool>,usize)> {
        if let Some(&STNode{key,left,right,left_sum,right_sum,..}) = self.arena.get(i) {
             let path: Vec<(Option<bool>,usize)> = {
                 if k <= cumulative + left_sum {
                     let mut path = if let Some(left_index) = left {
                         self.sample_path_from(k,left_index,cumulative, depth + 1)
                     }
                     else {Vec::with_capacity(depth)};
                     path.push((Some(false),i));
                     path
                }
                else if k < (cumulative + left_sum + key) {
                    let mut path = Vec::with_capacity(depth);
                    path.push((None,i));
                    path
                }
                else {
                    let mut path = if let Some(right_index) = right {
                        self.sample_path_from(k, right_index, cumulative + left_sum + key, depth + 1)
                    }
                    else {Vec::with_capacity(depth)};
                    path.push((Some(true),i));
                    path
                }

            };
            path
        }
        else {vec![]}
    }

    pub fn descend_index(&self,k:K) -> usize {
        let mut current = self.root;
        let mut next = Some(self.root);
        let mut cumulative: K = zero();
        while let Some(index) = next {
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
        // eprintln!("Removing {:?}",index);

        let last = self.send_to_back(index);
        let path = self.index_path(last);
        let key = self.arena[last].key;
        self.subtract_path(&path, key);
        let parent = self.arena[last].parent;
        // eprintln!("Switched");
        // eprintln!("{:?}",self);
        let mut children = self.unlink_back();
        // eprintln!("Switch Remove");
        // eprintln!("{:?}",self);
        if let Some((pb,pi)) = parent {
            for child in children {
                self.reinsert_node_at(child, Some(pi))
            }
        }
        else {
            for i in 0..children.len() {
                self.reinsert_node_at(children[i], children.get(i+1).map(|x| *x));
            }
        }

        // eprintln!("Inserted children");
        // eprintln!("{:?}",self);

        let value = self.arena.pop().unwrap().value;
        self.indecies.pop();

        // eprintln!("Attempting to balance");
        // eprintln!("{:?}",self);
        if self.arena.len() > 0 {
            self.balance_weight();
        }
        // eprintln!("{:?}",self);
        Some((key,value))
    }

    pub fn draw(&mut self) -> Option<(K,V)> {
        let draw: f64 = <f64 as NumCast>::from(self.sum()).unwrap() * random::<f64>();
        self.draw_specified(K::from(draw).unwrap())
    }

    pub fn draw_specified(&mut self,draw:K) -> Option<(K,V)> {
        let path = self.sample_path(draw);
        // eprintln!("{:?}",path);
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

    pub fn test_vec_large_random_f64() -> Vec<f64> {
        let mut rng = thread_rng();
        (0..10000).map(|_| rng.gen::<f64>()).collect()
    }

    pub fn test_vec_large_random_i32() -> Vec<i32> {
        let mut rng = thread_rng();
        (0..10000).map(|_| rng.gen::<i32>()).collect()
    }

    fn test_vec<K: ValidKey>(test_vec:Vec<K>)
    where
        Standard: Distribution<K>
    {
        let mut tree = WeightBalancedSearchTree::<K,usize>::index_tree(test_vec.clone());

        for _ in test_vec {
            eprintln!("{:?}",tree.draw());
        }
    }

    #[test]
    pub fn test_all() {
        let a = test_vec_f64();
        // let b = test_vec_usize();
        let c = test_vec_repetitive();
        let d = test_vec_empty();
        let e = test_vec_zero();
        let f = test_vec_large_random_f64();
        let g = test_vec_large_random_i32();

        test_vec(a);
        // test_vec(b);
        test_vec(c);
        test_vec(d);
        test_vec(e);
        test_vec(f);
        test_vec(g);

    }



}
