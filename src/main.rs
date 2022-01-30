extern crate minifb;
extern crate rayon;
extern crate regex;

use std::sync::atomic::AtomicUsize;
use std::time::Instant;
use minifb::{Key, Window, WindowOptions};
//use rand::distributions::{IndependentSample, Range};
use rayon::prelude::*;
use std::env;
use std::fs::File;
use std::io::Read;
use std::ops::Add;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Sub;
use std::cmp;

type Rfloat = f32;
type Rfixed = i32;

const RESOLUTION: usize = 768;
const TILE_DIM_SHIFT : usize = 6;
const TILE_DIM: usize = 1 << TILE_DIM_SHIFT;
const TILES_PER_LINE : usize = (RESOLUTION + TILE_DIM-1) / TILE_DIM;

// Rust conversion of Paul Bourke's C code:
// http://www.paulbourke.net/geometry/polygonise/
//
static EDGE_TABLE: [u32; 256] = [
    0x0, 0x109, 0x203, 0x30a, 0x406, 0x50f, 0x605, 0x70c, 0x80c, 0x905, 0xa0f, 0xb06, 0xc0a, 0xd03,
    0xe09, 0xf00, 0x190, 0x99, 0x393, 0x29a, 0x596, 0x49f, 0x795, 0x69c, 0x99c, 0x895, 0xb9f,
    0xa96, 0xd9a, 0xc93, 0xf99, 0xe90, 0x230, 0x339, 0x33, 0x13a, 0x636, 0x73f, 0x435, 0x53c,
    0xa3c, 0xb35, 0x83f, 0x936, 0xe3a, 0xf33, 0xc39, 0xd30, 0x3a0, 0x2a9, 0x1a3, 0xaa, 0x7a6,
    0x6af, 0x5a5, 0x4ac, 0xbac, 0xaa5, 0x9af, 0x8a6, 0xfaa, 0xea3, 0xda9, 0xca0, 0x460, 0x569,
    0x663, 0x76a, 0x66, 0x16f, 0x265, 0x36c, 0xc6c, 0xd65, 0xe6f, 0xf66, 0x86a, 0x963, 0xa69,
    0xb60, 0x5f0, 0x4f9, 0x7f3, 0x6fa, 0x1f6, 0xff, 0x3f5, 0x2fc, 0xdfc, 0xcf5, 0xfff, 0xef6,
    0x9fa, 0x8f3, 0xbf9, 0xaf0, 0x650, 0x759, 0x453, 0x55a, 0x256, 0x35f, 0x55, 0x15c, 0xe5c,
    0xf55, 0xc5f, 0xd56, 0xa5a, 0xb53, 0x859, 0x950, 0x7c0, 0x6c9, 0x5c3, 0x4ca, 0x3c6, 0x2cf,
    0x1c5, 0xcc, 0xfcc, 0xec5, 0xdcf, 0xcc6, 0xbca, 0xac3, 0x9c9, 0x8c0, 0x8c0, 0x9c9, 0xac3,
    0xbca, 0xcc6, 0xdcf, 0xec5, 0xfcc, 0xcc, 0x1c5, 0x2cf, 0x3c6, 0x4ca, 0x5c3, 0x6c9, 0x7c0,
    0x950, 0x859, 0xb53, 0xa5a, 0xd56, 0xc5f, 0xf55, 0xe5c, 0x15c, 0x55, 0x35f, 0x256, 0x55a,
    0x453, 0x759, 0x650, 0xaf0, 0xbf9, 0x8f3, 0x9fa, 0xef6, 0xfff, 0xcf5, 0xdfc, 0x2fc, 0x3f5,
    0xff, 0x1f6, 0x6fa, 0x7f3, 0x4f9, 0x5f0, 0xb60, 0xa69, 0x963, 0x86a, 0xf66, 0xe6f, 0xd65,
    0xc6c, 0x36c, 0x265, 0x16f, 0x66, 0x76a, 0x663, 0x569, 0x460, 0xca0, 0xda9, 0xea3, 0xfaa,
    0x8a6, 0x9af, 0xaa5, 0xbac, 0x4ac, 0x5a5, 0x6af, 0x7a6, 0xaa, 0x1a3, 0x2a9, 0x3a0, 0xd30,
    0xc39, 0xf33, 0xe3a, 0x936, 0x83f, 0xb35, 0xa3c, 0x53c, 0x435, 0x73f, 0x636, 0x13a, 0x33,
    0x339, 0x230, 0xe90, 0xf99, 0xc93, 0xd9a, 0xa96, 0xb9f, 0x895, 0x99c, 0x69c, 0x795, 0x49f,
    0x596, 0x29a, 0x393, 0x99, 0x190, 0xf00, 0xe09, 0xd03, 0xc0a, 0xb06, 0xa0f, 0x905, 0x80c,
    0x70c, 0x605, 0x50f, 0x406, 0x30a, 0x203, 0x109, 0x0,
];

static TRI_TABLE: [[i32; 16]; 256] = [
    [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 8, 3, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 1, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 8, 3, 9, 8, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 2, 10, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 8, 3, 1, 2, 10, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [9, 2, 10, 0, 2, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [2, 8, 3, 2, 10, 8, 10, 9, 8, -1, -1, -1, -1, -1, -1, -1],
    [3, 11, 2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 11, 2, 8, 11, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 9, 0, 2, 3, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 11, 2, 1, 9, 11, 9, 8, 11, -1, -1, -1, -1, -1, -1, -1],
    [3, 10, 1, 11, 10, 3, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 10, 1, 0, 8, 10, 8, 11, 10, -1, -1, -1, -1, -1, -1, -1],
    [3, 9, 0, 3, 11, 9, 11, 10, 9, -1, -1, -1, -1, -1, -1, -1],
    [9, 8, 10, 10, 8, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [4, 7, 8, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [4, 3, 0, 7, 3, 4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 1, 9, 8, 4, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [4, 1, 9, 4, 7, 1, 7, 3, 1, -1, -1, -1, -1, -1, -1, -1],
    [1, 2, 10, 8, 4, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [3, 4, 7, 3, 0, 4, 1, 2, 10, -1, -1, -1, -1, -1, -1, -1],
    [9, 2, 10, 9, 0, 2, 8, 4, 7, -1, -1, -1, -1, -1, -1, -1],
    [2, 10, 9, 2, 9, 7, 2, 7, 3, 7, 9, 4, -1, -1, -1, -1],
    [8, 4, 7, 3, 11, 2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [11, 4, 7, 11, 2, 4, 2, 0, 4, -1, -1, -1, -1, -1, -1, -1],
    [9, 0, 1, 8, 4, 7, 2, 3, 11, -1, -1, -1, -1, -1, -1, -1],
    [4, 7, 11, 9, 4, 11, 9, 11, 2, 9, 2, 1, -1, -1, -1, -1],
    [3, 10, 1, 3, 11, 10, 7, 8, 4, -1, -1, -1, -1, -1, -1, -1],
    [1, 11, 10, 1, 4, 11, 1, 0, 4, 7, 11, 4, -1, -1, -1, -1],
    [4, 7, 8, 9, 0, 11, 9, 11, 10, 11, 0, 3, -1, -1, -1, -1],
    [4, 7, 11, 4, 11, 9, 9, 11, 10, -1, -1, -1, -1, -1, -1, -1],
    [9, 5, 4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [9, 5, 4, 0, 8, 3, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 5, 4, 1, 5, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [8, 5, 4, 8, 3, 5, 3, 1, 5, -1, -1, -1, -1, -1, -1, -1],
    [1, 2, 10, 9, 5, 4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [3, 0, 8, 1, 2, 10, 4, 9, 5, -1, -1, -1, -1, -1, -1, -1],
    [5, 2, 10, 5, 4, 2, 4, 0, 2, -1, -1, -1, -1, -1, -1, -1],
    [2, 10, 5, 3, 2, 5, 3, 5, 4, 3, 4, 8, -1, -1, -1, -1],
    [9, 5, 4, 2, 3, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 11, 2, 0, 8, 11, 4, 9, 5, -1, -1, -1, -1, -1, -1, -1],
    [0, 5, 4, 0, 1, 5, 2, 3, 11, -1, -1, -1, -1, -1, -1, -1],
    [2, 1, 5, 2, 5, 8, 2, 8, 11, 4, 8, 5, -1, -1, -1, -1],
    [10, 3, 11, 10, 1, 3, 9, 5, 4, -1, -1, -1, -1, -1, -1, -1],
    [4, 9, 5, 0, 8, 1, 8, 10, 1, 8, 11, 10, -1, -1, -1, -1],
    [5, 4, 0, 5, 0, 11, 5, 11, 10, 11, 0, 3, -1, -1, -1, -1],
    [5, 4, 8, 5, 8, 10, 10, 8, 11, -1, -1, -1, -1, -1, -1, -1],
    [9, 7, 8, 5, 7, 9, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [9, 3, 0, 9, 5, 3, 5, 7, 3, -1, -1, -1, -1, -1, -1, -1],
    [0, 7, 8, 0, 1, 7, 1, 5, 7, -1, -1, -1, -1, -1, -1, -1],
    [1, 5, 3, 3, 5, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [9, 7, 8, 9, 5, 7, 10, 1, 2, -1, -1, -1, -1, -1, -1, -1],
    [10, 1, 2, 9, 5, 0, 5, 3, 0, 5, 7, 3, -1, -1, -1, -1],
    [8, 0, 2, 8, 2, 5, 8, 5, 7, 10, 5, 2, -1, -1, -1, -1],
    [2, 10, 5, 2, 5, 3, 3, 5, 7, -1, -1, -1, -1, -1, -1, -1],
    [7, 9, 5, 7, 8, 9, 3, 11, 2, -1, -1, -1, -1, -1, -1, -1],
    [9, 5, 7, 9, 7, 2, 9, 2, 0, 2, 7, 11, -1, -1, -1, -1],
    [2, 3, 11, 0, 1, 8, 1, 7, 8, 1, 5, 7, -1, -1, -1, -1],
    [11, 2, 1, 11, 1, 7, 7, 1, 5, -1, -1, -1, -1, -1, -1, -1],
    [9, 5, 8, 8, 5, 7, 10, 1, 3, 10, 3, 11, -1, -1, -1, -1],
    [5, 7, 0, 5, 0, 9, 7, 11, 0, 1, 0, 10, 11, 10, 0, -1],
    [11, 10, 0, 11, 0, 3, 10, 5, 0, 8, 0, 7, 5, 7, 0, -1],
    [11, 10, 5, 7, 11, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [10, 6, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 8, 3, 5, 10, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [9, 0, 1, 5, 10, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 8, 3, 1, 9, 8, 5, 10, 6, -1, -1, -1, -1, -1, -1, -1],
    [1, 6, 5, 2, 6, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 6, 5, 1, 2, 6, 3, 0, 8, -1, -1, -1, -1, -1, -1, -1],
    [9, 6, 5, 9, 0, 6, 0, 2, 6, -1, -1, -1, -1, -1, -1, -1],
    [5, 9, 8, 5, 8, 2, 5, 2, 6, 3, 2, 8, -1, -1, -1, -1],
    [2, 3, 11, 10, 6, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [11, 0, 8, 11, 2, 0, 10, 6, 5, -1, -1, -1, -1, -1, -1, -1],
    [0, 1, 9, 2, 3, 11, 5, 10, 6, -1, -1, -1, -1, -1, -1, -1],
    [5, 10, 6, 1, 9, 2, 9, 11, 2, 9, 8, 11, -1, -1, -1, -1],
    [6, 3, 11, 6, 5, 3, 5, 1, 3, -1, -1, -1, -1, -1, -1, -1],
    [0, 8, 11, 0, 11, 5, 0, 5, 1, 5, 11, 6, -1, -1, -1, -1],
    [3, 11, 6, 0, 3, 6, 0, 6, 5, 0, 5, 9, -1, -1, -1, -1],
    [6, 5, 9, 6, 9, 11, 11, 9, 8, -1, -1, -1, -1, -1, -1, -1],
    [5, 10, 6, 4, 7, 8, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [4, 3, 0, 4, 7, 3, 6, 5, 10, -1, -1, -1, -1, -1, -1, -1],
    [1, 9, 0, 5, 10, 6, 8, 4, 7, -1, -1, -1, -1, -1, -1, -1],
    [10, 6, 5, 1, 9, 7, 1, 7, 3, 7, 9, 4, -1, -1, -1, -1],
    [6, 1, 2, 6, 5, 1, 4, 7, 8, -1, -1, -1, -1, -1, -1, -1],
    [1, 2, 5, 5, 2, 6, 3, 0, 4, 3, 4, 7, -1, -1, -1, -1],
    [8, 4, 7, 9, 0, 5, 0, 6, 5, 0, 2, 6, -1, -1, -1, -1],
    [7, 3, 9, 7, 9, 4, 3, 2, 9, 5, 9, 6, 2, 6, 9, -1],
    [3, 11, 2, 7, 8, 4, 10, 6, 5, -1, -1, -1, -1, -1, -1, -1],
    [5, 10, 6, 4, 7, 2, 4, 2, 0, 2, 7, 11, -1, -1, -1, -1],
    [0, 1, 9, 4, 7, 8, 2, 3, 11, 5, 10, 6, -1, -1, -1, -1],
    [9, 2, 1, 9, 11, 2, 9, 4, 11, 7, 11, 4, 5, 10, 6, -1],
    [8, 4, 7, 3, 11, 5, 3, 5, 1, 5, 11, 6, -1, -1, -1, -1],
    [5, 1, 11, 5, 11, 6, 1, 0, 11, 7, 11, 4, 0, 4, 11, -1],
    [0, 5, 9, 0, 6, 5, 0, 3, 6, 11, 6, 3, 8, 4, 7, -1],
    [6, 5, 9, 6, 9, 11, 4, 7, 9, 7, 11, 9, -1, -1, -1, -1],
    [10, 4, 9, 6, 4, 10, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [4, 10, 6, 4, 9, 10, 0, 8, 3, -1, -1, -1, -1, -1, -1, -1],
    [10, 0, 1, 10, 6, 0, 6, 4, 0, -1, -1, -1, -1, -1, -1, -1],
    [8, 3, 1, 8, 1, 6, 8, 6, 4, 6, 1, 10, -1, -1, -1, -1],
    [1, 4, 9, 1, 2, 4, 2, 6, 4, -1, -1, -1, -1, -1, -1, -1],
    [3, 0, 8, 1, 2, 9, 2, 4, 9, 2, 6, 4, -1, -1, -1, -1],
    [0, 2, 4, 4, 2, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [8, 3, 2, 8, 2, 4, 4, 2, 6, -1, -1, -1, -1, -1, -1, -1],
    [10, 4, 9, 10, 6, 4, 11, 2, 3, -1, -1, -1, -1, -1, -1, -1],
    [0, 8, 2, 2, 8, 11, 4, 9, 10, 4, 10, 6, -1, -1, -1, -1],
    [3, 11, 2, 0, 1, 6, 0, 6, 4, 6, 1, 10, -1, -1, -1, -1],
    [6, 4, 1, 6, 1, 10, 4, 8, 1, 2, 1, 11, 8, 11, 1, -1],
    [9, 6, 4, 9, 3, 6, 9, 1, 3, 11, 6, 3, -1, -1, -1, -1],
    [8, 11, 1, 8, 1, 0, 11, 6, 1, 9, 1, 4, 6, 4, 1, -1],
    [3, 11, 6, 3, 6, 0, 0, 6, 4, -1, -1, -1, -1, -1, -1, -1],
    [6, 4, 8, 11, 6, 8, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [7, 10, 6, 7, 8, 10, 8, 9, 10, -1, -1, -1, -1, -1, -1, -1],
    [0, 7, 3, 0, 10, 7, 0, 9, 10, 6, 7, 10, -1, -1, -1, -1],
    [10, 6, 7, 1, 10, 7, 1, 7, 8, 1, 8, 0, -1, -1, -1, -1],
    [10, 6, 7, 10, 7, 1, 1, 7, 3, -1, -1, -1, -1, -1, -1, -1],
    [1, 2, 6, 1, 6, 8, 1, 8, 9, 8, 6, 7, -1, -1, -1, -1],
    [2, 6, 9, 2, 9, 1, 6, 7, 9, 0, 9, 3, 7, 3, 9, -1],
    [7, 8, 0, 7, 0, 6, 6, 0, 2, -1, -1, -1, -1, -1, -1, -1],
    [7, 3, 2, 6, 7, 2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [2, 3, 11, 10, 6, 8, 10, 8, 9, 8, 6, 7, -1, -1, -1, -1],
    [2, 0, 7, 2, 7, 11, 0, 9, 7, 6, 7, 10, 9, 10, 7, -1],
    [1, 8, 0, 1, 7, 8, 1, 10, 7, 6, 7, 10, 2, 3, 11, -1],
    [11, 2, 1, 11, 1, 7, 10, 6, 1, 6, 7, 1, -1, -1, -1, -1],
    [8, 9, 6, 8, 6, 7, 9, 1, 6, 11, 6, 3, 1, 3, 6, -1],
    [0, 9, 1, 11, 6, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [7, 8, 0, 7, 0, 6, 3, 11, 0, 11, 6, 0, -1, -1, -1, -1],
    [7, 11, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [7, 6, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [3, 0, 8, 11, 7, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 1, 9, 11, 7, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [8, 1, 9, 8, 3, 1, 11, 7, 6, -1, -1, -1, -1, -1, -1, -1],
    [10, 1, 2, 6, 11, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 2, 10, 3, 0, 8, 6, 11, 7, -1, -1, -1, -1, -1, -1, -1],
    [2, 9, 0, 2, 10, 9, 6, 11, 7, -1, -1, -1, -1, -1, -1, -1],
    [6, 11, 7, 2, 10, 3, 10, 8, 3, 10, 9, 8, -1, -1, -1, -1],
    [7, 2, 3, 6, 2, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [7, 0, 8, 7, 6, 0, 6, 2, 0, -1, -1, -1, -1, -1, -1, -1],
    [2, 7, 6, 2, 3, 7, 0, 1, 9, -1, -1, -1, -1, -1, -1, -1],
    [1, 6, 2, 1, 8, 6, 1, 9, 8, 8, 7, 6, -1, -1, -1, -1],
    [10, 7, 6, 10, 1, 7, 1, 3, 7, -1, -1, -1, -1, -1, -1, -1],
    [10, 7, 6, 1, 7, 10, 1, 8, 7, 1, 0, 8, -1, -1, -1, -1],
    [0, 3, 7, 0, 7, 10, 0, 10, 9, 6, 10, 7, -1, -1, -1, -1],
    [7, 6, 10, 7, 10, 8, 8, 10, 9, -1, -1, -1, -1, -1, -1, -1],
    [6, 8, 4, 11, 8, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [3, 6, 11, 3, 0, 6, 0, 4, 6, -1, -1, -1, -1, -1, -1, -1],
    [8, 6, 11, 8, 4, 6, 9, 0, 1, -1, -1, -1, -1, -1, -1, -1],
    [9, 4, 6, 9, 6, 3, 9, 3, 1, 11, 3, 6, -1, -1, -1, -1],
    [6, 8, 4, 6, 11, 8, 2, 10, 1, -1, -1, -1, -1, -1, -1, -1],
    [1, 2, 10, 3, 0, 11, 0, 6, 11, 0, 4, 6, -1, -1, -1, -1],
    [4, 11, 8, 4, 6, 11, 0, 2, 9, 2, 10, 9, -1, -1, -1, -1],
    [10, 9, 3, 10, 3, 2, 9, 4, 3, 11, 3, 6, 4, 6, 3, -1],
    [8, 2, 3, 8, 4, 2, 4, 6, 2, -1, -1, -1, -1, -1, -1, -1],
    [0, 4, 2, 4, 6, 2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 9, 0, 2, 3, 4, 2, 4, 6, 4, 3, 8, -1, -1, -1, -1],
    [1, 9, 4, 1, 4, 2, 2, 4, 6, -1, -1, -1, -1, -1, -1, -1],
    [8, 1, 3, 8, 6, 1, 8, 4, 6, 6, 10, 1, -1, -1, -1, -1],
    [10, 1, 0, 10, 0, 6, 6, 0, 4, -1, -1, -1, -1, -1, -1, -1],
    [4, 6, 3, 4, 3, 8, 6, 10, 3, 0, 3, 9, 10, 9, 3, -1],
    [10, 9, 4, 6, 10, 4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [4, 9, 5, 7, 6, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 8, 3, 4, 9, 5, 11, 7, 6, -1, -1, -1, -1, -1, -1, -1],
    [5, 0, 1, 5, 4, 0, 7, 6, 11, -1, -1, -1, -1, -1, -1, -1],
    [11, 7, 6, 8, 3, 4, 3, 5, 4, 3, 1, 5, -1, -1, -1, -1],
    [9, 5, 4, 10, 1, 2, 7, 6, 11, -1, -1, -1, -1, -1, -1, -1],
    [6, 11, 7, 1, 2, 10, 0, 8, 3, 4, 9, 5, -1, -1, -1, -1],
    [7, 6, 11, 5, 4, 10, 4, 2, 10, 4, 0, 2, -1, -1, -1, -1],
    [3, 4, 8, 3, 5, 4, 3, 2, 5, 10, 5, 2, 11, 7, 6, -1],
    [7, 2, 3, 7, 6, 2, 5, 4, 9, -1, -1, -1, -1, -1, -1, -1],
    [9, 5, 4, 0, 8, 6, 0, 6, 2, 6, 8, 7, -1, -1, -1, -1],
    [3, 6, 2, 3, 7, 6, 1, 5, 0, 5, 4, 0, -1, -1, -1, -1],
    [6, 2, 8, 6, 8, 7, 2, 1, 8, 4, 8, 5, 1, 5, 8, -1],
    [9, 5, 4, 10, 1, 6, 1, 7, 6, 1, 3, 7, -1, -1, -1, -1],
    [1, 6, 10, 1, 7, 6, 1, 0, 7, 8, 7, 0, 9, 5, 4, -1],
    [4, 0, 10, 4, 10, 5, 0, 3, 10, 6, 10, 7, 3, 7, 10, -1],
    [7, 6, 10, 7, 10, 8, 5, 4, 10, 4, 8, 10, -1, -1, -1, -1],
    [6, 9, 5, 6, 11, 9, 11, 8, 9, -1, -1, -1, -1, -1, -1, -1],
    [3, 6, 11, 0, 6, 3, 0, 5, 6, 0, 9, 5, -1, -1, -1, -1],
    [0, 11, 8, 0, 5, 11, 0, 1, 5, 5, 6, 11, -1, -1, -1, -1],
    [6, 11, 3, 6, 3, 5, 5, 3, 1, -1, -1, -1, -1, -1, -1, -1],
    [1, 2, 10, 9, 5, 11, 9, 11, 8, 11, 5, 6, -1, -1, -1, -1],
    [0, 11, 3, 0, 6, 11, 0, 9, 6, 5, 6, 9, 1, 2, 10, -1],
    [11, 8, 5, 11, 5, 6, 8, 0, 5, 10, 5, 2, 0, 2, 5, -1],
    [6, 11, 3, 6, 3, 5, 2, 10, 3, 10, 5, 3, -1, -1, -1, -1],
    [5, 8, 9, 5, 2, 8, 5, 6, 2, 3, 8, 2, -1, -1, -1, -1],
    [9, 5, 6, 9, 6, 0, 0, 6, 2, -1, -1, -1, -1, -1, -1, -1],
    [1, 5, 8, 1, 8, 0, 5, 6, 8, 3, 8, 2, 6, 2, 8, -1],
    [1, 5, 6, 2, 1, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 3, 6, 1, 6, 10, 3, 8, 6, 5, 6, 9, 8, 9, 6, -1],
    [10, 1, 0, 10, 0, 6, 9, 5, 0, 5, 6, 0, -1, -1, -1, -1],
    [0, 3, 8, 5, 6, 10, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [10, 5, 6, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [11, 5, 10, 7, 5, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [11, 5, 10, 11, 7, 5, 8, 3, 0, -1, -1, -1, -1, -1, -1, -1],
    [5, 11, 7, 5, 10, 11, 1, 9, 0, -1, -1, -1, -1, -1, -1, -1],
    [10, 7, 5, 10, 11, 7, 9, 8, 1, 8, 3, 1, -1, -1, -1, -1],
    [11, 1, 2, 11, 7, 1, 7, 5, 1, -1, -1, -1, -1, -1, -1, -1],
    [0, 8, 3, 1, 2, 7, 1, 7, 5, 7, 2, 11, -1, -1, -1, -1],
    [9, 7, 5, 9, 2, 7, 9, 0, 2, 2, 11, 7, -1, -1, -1, -1],
    [7, 5, 2, 7, 2, 11, 5, 9, 2, 3, 2, 8, 9, 8, 2, -1],
    [2, 5, 10, 2, 3, 5, 3, 7, 5, -1, -1, -1, -1, -1, -1, -1],
    [8, 2, 0, 8, 5, 2, 8, 7, 5, 10, 2, 5, -1, -1, -1, -1],
    [9, 0, 1, 5, 10, 3, 5, 3, 7, 3, 10, 2, -1, -1, -1, -1],
    [9, 8, 2, 9, 2, 1, 8, 7, 2, 10, 2, 5, 7, 5, 2, -1],
    [1, 3, 5, 3, 7, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 8, 7, 0, 7, 1, 1, 7, 5, -1, -1, -1, -1, -1, -1, -1],
    [9, 0, 3, 9, 3, 5, 5, 3, 7, -1, -1, -1, -1, -1, -1, -1],
    [9, 8, 7, 5, 9, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [5, 8, 4, 5, 10, 8, 10, 11, 8, -1, -1, -1, -1, -1, -1, -1],
    [5, 0, 4, 5, 11, 0, 5, 10, 11, 11, 3, 0, -1, -1, -1, -1],
    [0, 1, 9, 8, 4, 10, 8, 10, 11, 10, 4, 5, -1, -1, -1, -1],
    [10, 11, 4, 10, 4, 5, 11, 3, 4, 9, 4, 1, 3, 1, 4, -1],
    [2, 5, 1, 2, 8, 5, 2, 11, 8, 4, 5, 8, -1, -1, -1, -1],
    [0, 4, 11, 0, 11, 3, 4, 5, 11, 2, 11, 1, 5, 1, 11, -1],
    [0, 2, 5, 0, 5, 9, 2, 11, 5, 4, 5, 8, 11, 8, 5, -1],
    [9, 4, 5, 2, 11, 3, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [2, 5, 10, 3, 5, 2, 3, 4, 5, 3, 8, 4, -1, -1, -1, -1],
    [5, 10, 2, 5, 2, 4, 4, 2, 0, -1, -1, -1, -1, -1, -1, -1],
    [3, 10, 2, 3, 5, 10, 3, 8, 5, 4, 5, 8, 0, 1, 9, -1],
    [5, 10, 2, 5, 2, 4, 1, 9, 2, 9, 4, 2, -1, -1, -1, -1],
    [8, 4, 5, 8, 5, 3, 3, 5, 1, -1, -1, -1, -1, -1, -1, -1],
    [0, 4, 5, 1, 0, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [8, 4, 5, 8, 5, 3, 9, 0, 5, 0, 3, 5, -1, -1, -1, -1],
    [9, 4, 5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [4, 11, 7, 4, 9, 11, 9, 10, 11, -1, -1, -1, -1, -1, -1, -1],
    [0, 8, 3, 4, 9, 7, 9, 11, 7, 9, 10, 11, -1, -1, -1, -1],
    [1, 10, 11, 1, 11, 4, 1, 4, 0, 7, 4, 11, -1, -1, -1, -1],
    [3, 1, 4, 3, 4, 8, 1, 10, 4, 7, 4, 11, 10, 11, 4, -1],
    [4, 11, 7, 9, 11, 4, 9, 2, 11, 9, 1, 2, -1, -1, -1, -1],
    [9, 7, 4, 9, 11, 7, 9, 1, 11, 2, 11, 1, 0, 8, 3, -1],
    [11, 7, 4, 11, 4, 2, 2, 4, 0, -1, -1, -1, -1, -1, -1, -1],
    [11, 7, 4, 11, 4, 2, 8, 3, 4, 3, 2, 4, -1, -1, -1, -1],
    [2, 9, 10, 2, 7, 9, 2, 3, 7, 7, 4, 9, -1, -1, -1, -1],
    [9, 10, 7, 9, 7, 4, 10, 2, 7, 8, 7, 0, 2, 0, 7, -1],
    [3, 7, 10, 3, 10, 2, 7, 4, 10, 1, 10, 0, 4, 0, 10, -1],
    [1, 10, 2, 8, 7, 4, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [4, 9, 1, 4, 1, 7, 7, 1, 3, -1, -1, -1, -1, -1, -1, -1],
    [4, 9, 1, 4, 1, 7, 0, 8, 1, 8, 7, 1, -1, -1, -1, -1],
    [4, 0, 3, 7, 4, 3, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [4, 8, 7, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [9, 10, 8, 10, 11, 8, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [3, 0, 9, 3, 9, 11, 11, 9, 10, -1, -1, -1, -1, -1, -1, -1],
    [0, 1, 10, 0, 10, 8, 8, 10, 11, -1, -1, -1, -1, -1, -1, -1],
    [3, 1, 10, 11, 3, 10, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 2, 11, 1, 11, 9, 9, 11, 8, -1, -1, -1, -1, -1, -1, -1],
    [3, 0, 9, 3, 9, 11, 1, 2, 9, 2, 11, 9, -1, -1, -1, -1],
    [0, 2, 11, 8, 0, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [3, 2, 11, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [2, 3, 8, 2, 8, 10, 10, 8, 9, -1, -1, -1, -1, -1, -1, -1],
    [9, 10, 2, 0, 9, 2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [2, 3, 8, 2, 8, 10, 0, 1, 8, 1, 10, 8, -1, -1, -1, -1],
    [1, 10, 2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [1, 3, 8, 9, 1, 8, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 9, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [0, 3, 8, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
    [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
];

#[derive(Copy, Clone, Debug)]
struct Vector2 {
    x: Rfloat,
    y: Rfloat,
}
struct Point2 {
    x: Rfixed,
    y: Rfixed,
}

#[derive(Copy, Clone, Debug)]
struct Vector3 {
    x: Rfloat,
    y: Rfloat,
    z: Rfloat,
}
struct Vector4 {
    x: Rfloat,
    y: Rfloat,
    z: Rfloat,
    w: Rfloat,
}

#[derive(Copy, Clone)]
struct Matrix4 {
    data: [[Rfloat; 4]; 4],
}

#[derive(Copy, Clone)]
struct Vertex {
    pos: Vector3,
    normal: Vector3,
    //color : Vector3
    uv: Vector2,
}

impl Default for Vertex {
    fn default() -> Vertex {
        Vertex {
            pos: ZERO_VECTOR,
            normal: ZERO_VECTOR,
            uv: ZERO_VECTOR2
        }
    }
}

#[derive(Copy, Clone)]
struct Triangle {
    v0: usize,
    v1: usize,
    v2: usize,
    color : Vector3
}

impl Default for Triangle {
    fn default() -> Self {
        Triangle { v0 : 0, v1 : 0, v2 : 0, color : ZERO_VECTOR }
    }
}

struct GridVertex {
    p: Vertex,
    val: Rfloat,
}

struct GridCell {
    corners: [usize; 8], // GridVertex indices
}

struct Grid {
    verts: Vec<GridVertex>,
    cells: Vec<GridCell>,
    res: usize,
}

struct Blob {
    center: Vector3,
    radius: Rfloat,
}

const ZERO_VECTOR: Vector3 = Vector3 {
    x: 0.0,
    y: 0.0,
    z: 0.0,
};

const ZERO_VECTOR2: Vector2 = Vector2 { x: 0.0, y: 0.0 };

struct ScreenTile {
    triangles : Vec<usize>,
    min_x : usize,
    max_x : usize,
    min_y : usize,
    max_y : usize
}

impl Vector2 {
    fn new(vx: Rfloat, vy: Rfloat) -> Vector2 {
        Vector2 { x: vx, y: vy }
    }
}

impl Vector3 {
    fn new(vx: Rfloat, vy: Rfloat, vz: Rfloat) -> Vector3 {
        Vector3 {
            x: vx,
            y: vy,
            z: vz,
        }
    }
    fn normalize(&mut self) {
        let len_sqr = dot(self, self);
        if len_sqr > std::f32::EPSILON {
            let oo_len = 1.0 / len_sqr.sqrt();
            self.x *= oo_len;
            self.y *= oo_len;
            self.z *= oo_len;
        }
    }
}

impl Sub for Vector3 {
    type Output = Vector3;
    fn sub(self: Vector3, b: Vector3) -> Vector3 {
        Vector3 {
            x: self.x - b.x,
            y: self.y - b.y,
            z: self.z - b.z,
        }
    }
}
impl Add for Vector3 {
    type Output = Vector3;
    fn add(self: Vector3, b: Vector3) -> Vector3 {
        Vector3 {
            x: self.x + b.x,
            y: self.y + b.y,
            z: self.z + b.z,
        }
    }
}
impl Div<Rfloat> for Vector3 {
    type Output = Vector3;
    fn div(self: Vector3, s: Rfloat) -> Vector3 {
        Vector3 {
            x: self.x / s,
            y: self.y / s,
            z: self.z / s,
        }
    }
}
impl Mul<Rfloat> for Vector3 {
    type Output = Vector3;
    fn mul(self: Vector3, s: Rfloat) -> Vector3 {
        Vector3 {
            x: self.x * s,
            y: self.y * s,
            z: self.z * s,
        }
    }
}

impl Matrix4 {
    fn new(
        m00: Rfloat,
        m01: Rfloat,
        m02: Rfloat,
        m03: Rfloat,
        m10: Rfloat,
        m11: Rfloat,
        m12: Rfloat,
        m13: Rfloat,
        m20: Rfloat,
        m21: Rfloat,
        m22: Rfloat,
        m23: Rfloat,
        m30: Rfloat,
        m31: Rfloat,
        m32: Rfloat,
        m33: Rfloat,
    ) -> Matrix4 {
        Matrix4 {
            data: [
                [m00, m01, m02, m03],
                [m10, m11, m12, m13],
                [m20, m21, m22, m23],
                [m30, m31, m32, m33],
            ],
        }
    }
}

macro_rules! mtx_elem {
    ($a : ident, $b : ident, $r : expr, $c : expr) => {
        $a.data[$r][0] * $b.data[0][$c]
            + $a.data[$r][1] * $b.data[1][$c]
            + $a.data[$r][2] * $b.data[2][$c]
            + $a.data[$r][3] * $b.data[3][$c]
    };
}
/*macro_rules! mtx_row {
    ($a : ident, $b : ident, $r : expr) => (
        mtx_elem!($a, $b, $r, 0), mtx_elem!($a, $b, $r, 1), mtx_elem!($a, $b, $r, 2), mtx_elem!($a, $b, $r, 3)
    )
}*/

macro_rules! corner_offset {
    ($x : expr, $y : expr, $z : expr, $res : expr) => {
        ($z * $res * $res) + ($y * $res) + $x
    };
}

macro_rules! cell_corner {
    ($gv : expr, $grid : expr, $c : expr) => {
        $gv[$grid.corners[$c]]
    };
}

macro_rules! cell_interp {
    ($gv : expr, $grid : expr, $isolevel : expr, $v0 : expr, $v1 : expr) => {{
        let tmp_c0 = &cell_corner!($gv, $grid, $v0);
        let tmp_c1 = &cell_corner!($gv, $grid, $v1);
        vertex_interp($isolevel, tmp_c0.p, tmp_c1.p, tmp_c0.val, tmp_c1.val)
    }};
}

impl Mul for Matrix4 {
    type Output = Matrix4;
    fn mul(self: Matrix4, b: Matrix4) -> Matrix4 {
        Matrix4::new(
            mtx_elem!(self, b, 0, 0),
            mtx_elem!(self, b, 0, 1),
            mtx_elem!(self, b, 0, 2),
            mtx_elem!(self, b, 0, 3),
            mtx_elem!(self, b, 1, 0),
            mtx_elem!(self, b, 1, 1),
            mtx_elem!(self, b, 1, 2),
            mtx_elem!(self, b, 1, 3),
            mtx_elem!(self, b, 2, 0),
            mtx_elem!(self, b, 2, 1),
            mtx_elem!(self, b, 2, 2),
            mtx_elem!(self, b, 2, 3),
            mtx_elem!(self, b, 3, 0),
            mtx_elem!(self, b, 3, 1),
            mtx_elem!(self, b, 3, 2),
            mtx_elem!(self, b, 3, 3),
        )
    }
}

fn transform_point4(v: &Vector3, m: &Matrix4) -> Vector4 {
    Vector4 {
        x: v.x * m.data[0][0] + v.y * m.data[1][0] + v.z * m.data[2][0] + m.data[3][0],
        y: v.x * m.data[0][1] + v.y * m.data[1][1] + v.z * m.data[2][1] + m.data[3][1],
        z: v.x * m.data[0][2] + v.y * m.data[1][2] + v.z * m.data[2][2] + m.data[3][2],
        w: v.x * m.data[0][3] + v.y * m.data[1][3] + v.z * m.data[2][3] + m.data[3][3],
    }
}

fn dot(a: &Vector3, b: &Vector3) -> Rfloat {
    a.x * b.x + a.y * b.y + a.z * b.z
}

fn cross(a: &Vector3, b: &Vector3) -> Vector3 {
    Vector3 {
        x: a.y * b.z - a.z * b.y,
        y: a.z * b.x - a.x * b.z,
        z: a.x * b.y - a.y * b.x,
    }
}

fn min_vec(a: &Vector3, b: &Vector3) -> Vector3 {
    Vector3 {
        x: a.x.min(b.x),
        y: a.y.min(b.y),
        z: a.z.min(b.z),
    }
}
fn max_vec(a: &Vector3, b: &Vector3) -> Vector3 {
    Vector3 {
        x: a.x.max(b.x),
        y: a.y.max(b.y),
        z: a.z.max(b.z),
    }
}

fn triangle_normal(v0: &Vector3, v1: &Vector3, v2: &Vector3) -> Vector3 {
    let mut n = cross(&(*v1 - *v0), &(*v2 - *v0));
    n.normalize();
    n
}

fn perspective_projection_matrix(
    vertical_fov_deg: Rfloat,
    aspect: Rfloat,
    near: Rfloat,
    far: Rfloat,
) -> Matrix4 {
    let tfov = (vertical_fov_deg.to_radians() / 2.0).tan();
    let m00 = 1.0 / (aspect * tfov);
    let m11 = 1.0 / tfov;
    let oo_fmn = 1.0 / (far - near);
    let m22 = -(far + near) * oo_fmn;
    let m23 = -(2.0 * far * near) * oo_fmn;

    Matrix4::new(
        m00, 0.0, 0.0, 0.0, 0.0, m11, 0.0, 0.0, 0.0, 0.0, m22, m23, 0.0, 0.0, -1.0, 0.0,
    )
}

fn viewport_matrix(w: Rfloat, h: Rfloat) -> Matrix4 {
    let wh = w * 0.5;
    let hh = h * 0.5;
    Matrix4::new(
        wh, 0.0, 0.0, 0.0, 0.0, hh, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, wh, hh, 0.0, 1.0,
    )
}

fn view_matrix(cam_dist: Rfloat) -> Matrix4 {
    Matrix4::new(
        1.0, 0.0, 0.0, 0.0, 
        0.0, 1.0, 0.0, 0.0, 
        0.0, 0.0, 1.0, 0.0, 
        0.0, 0.0, -cam_dist, 1.0,
    )
}

fn rotx_matrix(degs: Rfloat) -> Matrix4 {
    let rads = degs.to_radians();
    let c = rads.cos();
    let s = rads.sin();

    Matrix4::new(
        1.0, 0.0, 0.0, 0.0, 
        0.0, c, -s, 0.0, 
        0.0, s, c, 0.0, 
        0.0, 0.0, 0.0, 1.0,
    )
}
fn roty_matrix(degs: Rfloat) -> Matrix4 {
    let rads = degs.to_radians();
    let c = rads.cos();
    let s = rads.sin();

    Matrix4::new(
        c, 0.0, s, 0.0, 
        0.0, 1.0, 0.0, 0.0, 
        -s, 0.0, c, 0.0, 
        0.0, 0.0, 0.0, 1.0,
    )
}
fn rotz_matrix(degs: Rfloat) -> Matrix4 {
    let rads = degs.to_radians();
    let c = rads.cos();
    let s = rads.sin();

    Matrix4::new(
        c, -s, 0.0, 0.0, 
        s, c, 0.0, 0.0, 
        0.0, 0.0, 1.0, 0.0, 
        0.0, 0.0, 0.0, 1.0,
    )
}


/*
   Linearly interpolate the position where an isosurface cuts
   an edge between two vertices, each with their own scalar value
*/
fn vertex_interp(
    isolevel: Rfloat,
    p1: Vertex,
    p2: Vertex,
    valp1: Rfloat,
    valp2: Rfloat,
) -> Vertex {
    if (isolevel - valp1).abs() < 0.00001 {
        return p1;
    }
    if (isolevel - valp2).abs() < 0.00001 {
        return p2;
    }
    if (valp1 - valp2).abs() < 0.00001 {
        return p1;
    }
    let mu = (isolevel - valp1) / (valp2 - valp1);

    Vertex { pos: p1.pos + ((p2.pos - p1.pos) * mu), ..Default::default() }
}

struct UnsafeSlice<T> {
    ptr : *mut T,
    size : AtomicUsize
}
unsafe impl<T> Sync for UnsafeSlice<T> {}
impl<T> UnsafeSlice<T> {
    fn push(self : &UnsafeSlice<T>, v : T) {
        let index = self.size.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        unsafe {
            *self.ptr.add(index) = v;
        }
    }
    fn push3(self : &UnsafeSlice<T>, a : T, b : T, c : T) -> usize {
        let index = self.size.fetch_add(3, std::sync::atomic::Ordering::SeqCst);
        unsafe {
            *self.ptr.add(index) = a;
            *self.ptr.add(index + 1) = b;
            *self.ptr.add(index + 2) = c;
        }
        index
    }    
    fn len(self : &UnsafeSlice<T>) -> usize {
        self.size.load(std::sync::atomic::Ordering::SeqCst)
    }
}

fn polygonise(
    grid: &GridCell,
    grid_verts: &[GridVertex],
    isolevel: Rfloat,
    out_verts : &UnsafeSlice<Vertex>,
    out_tris: &UnsafeSlice<Triangle>) {

    let mut cubeindex = 0;
    for corner in 0..8 {
        if cell_corner!(grid_verts, grid, corner).val < isolevel {
            cubeindex |= 1 << corner;
        }
    }
 
    /* Cube is entirely in/out of the surface */
    if EDGE_TABLE[cubeindex] == 0 {
        return;
    }

    let mut vertlist = [Vertex::default(); 12];

    const INTERP_DATA : [(usize, usize); 12] = [   (0, 1), (1, 2), (2, 3), (3, 0),
                            (4, 5), (5, 6), (6, 7), (7, 4),
                            (0, 4), (1, 5), (2, 6), (3, 7) ];
    // Faster than map to vector (no allocation)
    INTERP_DATA.iter().enumerate().for_each(|v| {
        if EDGE_TABLE[cubeindex] & (1 << v.0) != 0 {
            vertlist[v.0] = cell_interp!(grid_verts, grid, isolevel, v.1.0, v.1.1);
        }
    });

    /* Create the triangle */
    let mut i = 0;
    
    while TRI_TABLE[cubeindex][i] != -1 {
        let first_vertex_index = out_verts.push3(vertlist[TRI_TABLE[cubeindex][i] as usize],
            vertlist[TRI_TABLE[cubeindex][i + 1] as usize],
            vertlist[TRI_TABLE[cubeindex][i + 2] as usize]);

        out_tris.push(Triangle {
            v0: first_vertex_index,
            v1: first_vertex_index + 1,
            v2: first_vertex_index + 2,
            color : ZERO_VECTOR
        });
        i += 3;
    }
}

fn polygonise_chunk(
    grid_chunk: &[GridCell],
    grid_verts: &[GridVertex],
    isolevel: Rfloat,
    out_verts : &UnsafeSlice<Vertex>,
    out_tris: &UnsafeSlice<Triangle>) {
    for cell in grid_chunk {
        polygonise(cell, grid_verts, isolevel, out_verts, out_tris); 
    }
}

fn load_ply(file_name: &str) -> (Vec<Vertex>, Vec<Triangle>) {
    let path = std::path::Path::new(file_name);

    let mut vert_list = Vec::new();
    let mut num_verts = 0;
    let mut num_faces = 0;
    let mut triangle_list = Vec::new();

    let mut f = match File::open(&path) {
        Err(why) => panic!(
            "Failed to load {} - {}",
            file_name,
            why
        ),
        Ok(f) => f,
    };

    let mut file_data = String::new();
    if let Err(why) = f.read_to_string(&mut file_data) { 
        panic!("Failed to load {} - {}", file_name, why) 
    };

    let mut lines = file_data.lines();
    let mut num_vertex_props = 0;

    #[derive(PartialEq)]
    enum ParserState {
        None,
        VertexProps,
        FaceProps,
        Verts,
        Faces,
    }

    let mut parse_state = ParserState::None;
    let mut min_v = Vector3::new(std::f32::MAX, std::f32::MAX, std::f32::MAX);
    let mut max_v = Vector3::new(std::f32::MIN, std::f32::MIN, std::f32::MIN);

    loop {
        match lines.next() {
            Some("") => (),
            Some(line) => {
                let words: Vec<&str> = line.split(' ').collect();
                if words[0] == "element" {
                    if words[1] == "vertex" {
                        num_verts = words[2].parse().unwrap();
                        println!("Num verts {:?}", num_verts);
                        parse_state = ParserState::VertexProps;
                    } else if words[1] == "face" {
                        num_faces = words[2].parse().unwrap();
                        println!("Num faces {:?}", num_faces);
                        parse_state = ParserState::FaceProps;
                    }
                } else if words[0] == "property" && parse_state == ParserState::VertexProps {
                    num_vertex_props += 1;
                    println!("num vertex props {:?}", num_vertex_props);
                } else if words[0] == "end_header" {
                    parse_state = ParserState::Verts;
                } else if parse_state == ParserState::Verts {
                    let mut vertex_props: Vec<Rfloat> = Vec::new();
                    for vp in words.iter().take(num_vertex_props) {
                        //println!("Parsing: {:?}", words[i]);
                        vertex_props.push(vp.parse::<Rfloat>().unwrap() * 32.0);
                    }
                    vert_list.push(Vertex {
                        pos: Vector3::new(vertex_props[0], vertex_props[1], vertex_props[2]),
                        normal: ZERO_VECTOR,
                        uv: Vector2::new(0.0, 0.0),
                    });
                    min_v = min_vec(&min_v, &vert_list[vert_list.len() - 1].pos);
                    max_v = max_vec(&max_v, &vert_list[vert_list.len() - 1].pos);

                    if vert_list.len() == num_verts {
                        println!("Verts parsed");
                        parse_state = ParserState::Faces;
                    }
                } else if parse_state == ParserState::Faces {
                    let tri = Triangle {
                        v0: words[3].parse::<usize>().unwrap(),
                        v1: words[2].parse::<usize>().unwrap(),
                        v2: words[1].parse::<usize>().unwrap(),
                        color : ZERO_VECTOR
                    };
                    triangle_list.push(tri);
                    if triangle_list.len() == num_faces {
                        break;
                    }
                }
            }
            None => panic!("Couldn't parse {}", file_name),
        }
    }

    let center = (min_v + max_v) / 2.0;
    for v in &mut vert_list {
        v.pos = v.pos - center;
    }

    (vert_list, triangle_list)
}

fn calc_blob_mesh(
    grid: &Grid,
    isolevel: Rfloat,
    out_verts : &mut Vec<Vertex>,
    out_tris: &mut Vec<Triangle>) {

    let vert_slice = UnsafeSlice { ptr : out_verts.as_mut_ptr(), size : AtomicUsize::new(0) };
    let tri_slice = UnsafeSlice { ptr : out_tris.as_mut_ptr(), size : AtomicUsize::new(0) };

    //grid.cells.iter().for_each(|cell| polygonise(cell, &grid.verts, isolevel, field_func, 
        //&mut vert_slice, &mut tri_slice));

    grid.cells
        .par_chunks(64)
        .for_each(|chunk| {
            polygonise_chunk(chunk, &grid.verts, isolevel, 
                &vert_slice, &tri_slice);
        });

    out_verts.resize(vert_slice.len(), Vertex::default());
    out_tris.resize(tri_slice.len(), Triangle::default());
}

fn build_grid(grid: &mut Grid) {
    const GRID_SCALE : Rfloat = 110.0;
    let mut x_pos = -GRID_SCALE;
    let x_step = (GRID_SCALE - x_pos) / grid.res as Rfloat;
    for _x in 0..grid.res {
        let mut y_pos = -GRID_SCALE;
        for _y in 0..grid.res {
            let mut z_pos = -GRID_SCALE;
            for _z in 0..grid.res {
                let v = Vertex {
                    pos: Vector3::new(x_pos, y_pos, z_pos),
                    normal: ZERO_VECTOR,
                    uv: ZERO_VECTOR2,
                };
                grid.verts.push(GridVertex { p: v, val: 0.0 });

                z_pos += x_step;
            }
            y_pos += x_step;
        }
        x_pos += x_step;
    }

    for x in 0..grid.res - 1 {
        for y in 0..grid.res - 1 {
            for z in 0..grid.res - 1 {
                let gc = GridCell {
                    corners: [
                        corner_offset!(x, y, z, grid.res),
                        corner_offset!(x + 1, y, z, grid.res),
                        corner_offset!(x + 1, y + 1, z, grid.res),
                        corner_offset!(x, y + 1, z, grid.res),
                        corner_offset!(x, y, z + 1, grid.res),
                        corner_offset!(x + 1, y, z + 1, grid.res),
                        corner_offset!(x + 1, y + 1, z + 1, grid.res),
                        corner_offset!(x, y + 1, z + 1, grid.res),
                    ],
                };
                grid.cells.push(gc);
            }
        }
    }
}

fn field_function(point: Vector3, blobs: &[Blob]) -> f32 {
    let mut sum = -1.0;
    for blob in blobs {
        let p = point * (1.0 / blob.radius);

        let to_vertex = blob.center - p;
        let sqr_dist = dot(&to_vertex, &to_vertex);
        sum += 1.0 / sqr_dist;
    }
    sum
}

fn update_blobs(grid: &mut Grid, blobs: &[Blob]) {
    for gv in grid.verts.iter_mut() {
        gv.val = 0.0;
        gv.p.normal = ZERO_VECTOR;

        gv.val = field_function(gv.p.pos, blobs);
    }

    /*  for ref blob in blobs
    {
        let sqrRadius = blob.radius * blob.radius;
        for gv in grid.verts.iter_mut()
        {
            let toVertex = blob.center - gv.p.pos;
            let sqrDist = dot(&toVertex, &toVertex);
            gv.val += sqrRadius / sqrDist;

            let den = sqrDist * sqrDist;
            //let ns = sqrRadius / den;
            let ns = toVertex * -2.0;
            gv.p.normal = gv.p.normal + (ns / den);

            //let ns = sqrRadius / (sqrDist * sqrDist);
            //gv.p.normal = gv.p.normal + (toVertex * ns);
            gv.p.normal.normalize();
        }
    }*/
}

fn min3<T: PartialOrd>(a: T, b: T, c: T) -> T {
    if a < b {
        if a < c {
            a
        } else {
            c
        }
    } else if b < c {
        b
    } else {
        c
    }
}
fn max3<T: PartialOrd>(a: T, b: T, c: T) -> T {
    if a > b {
        if a > c {
            a
        } else {
            c
        }
    } else if b > c {
        b
    } else {
        c
    }
}
fn minxy(
    (x0, y0): (Rfixed, Rfixed),
    (x1, y1): (Rfixed, Rfixed),
    (x2, y2): (Rfixed, Rfixed),
) -> (Rfixed, Rfixed) {
    let minx = min3(x0, x1, x2);
    let miny = min3(y0, y1, y2);
    ((minx as Rfixed + 0xF) >> 4, (miny as Rfixed + 0xF) >> 4)
}
fn maxxy(
    (x0, y0): (Rfixed, Rfixed),
    (x1, y1): (Rfixed, Rfixed),
    (x2, y2): (Rfixed, Rfixed),
) -> (Rfixed, Rfixed) {
    let maxx = max3(x0, x1, x2);
    let maxy = max3(y0, y1, y2);
    ((maxx as Rfixed + 0xF) >> 4, (maxy as Rfixed + 0xF) >> 4)
}

// 28.4
fn as_fixed_pt(x: Rfloat) -> Rfixed {
    (16.0 * x) as Rfixed
}

fn orient2d(a: &Point2, b: &Point2, c: &Point2) -> Rfixed {
    (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)
}

// deltas are a bit confusing, but that's because we want to re-use edge functions
// dx is end-start (ie. >0 if going "right")
// dy is start-end (ie. >0 if going "up")
fn is_edge_top_left(dx : Rfixed, dy : Rfixed) -> bool {
    dy > 0 || (dy == 0 && dx > 0)
}

fn draw_triangle(
    v0: &Vertex,
    v1: &Vertex,
    v2: &Vertex,
    r: u32,
    g: u32,
    b: u32,
    win_min: &Point2,
    win_max: &Point2,
    buffer: *mut u32,
    depth_buffer: *mut f32) {
    let x0 = as_fixed_pt(v0.pos.x);
    let y0 = as_fixed_pt(v0.pos.y);
    let x1 = as_fixed_pt(v1.pos.x);
    let y1 = as_fixed_pt(v1.pos.y);
    let x2 = as_fixed_pt(v2.pos.x);
    let y2 = as_fixed_pt(v2.pos.y);

    let p0 = Point2 { x: x0, y: y0 };
    let p1 = Point2 { x: x1, y: y1 };
    let p2 = Point2 { x: x2, y: y2 };

    // Clamp to bounding box
    let (mut minx, mut miny) = minxy((x0, y0), (x1, y1), (x2, y2));
    let (mut maxx, mut maxy) = maxxy((x0, y0), (x1, y1), (x2, y2));

    if maxx <= minx || maxy <= miny {
        return;
    }

    // Backface culling
    let tri_a2 = orient2d(&p0, &p1, &p2);
    if tri_a2 <= 0 {
        return;
    }

    if minx < win_min.x {
        minx = win_min.x
    };
    if miny < win_min.y {
        miny = win_min.y
    };
    if maxx > win_max.x {
        maxx = win_max.x
    };
    if maxy > win_max.y {
        maxy = win_max.y
    };

    let mut fb_offset = (miny as usize) * RESOLUTION;
    let inv_tri_a2 = 1.0 / tri_a2 as f32;

    let dx10 = x1 - x0;
    let dy01 = y0 - y1;
    let dx21 = x2 - x1;
    let dy12 = y1 - y2;
    let dx02 = x0 - x2;
    let dy20 = y2 - y0;
    
    // Precalc deltas to save some multiplications
    // in the inner loop
    /*let u10 = v1.uv.x - v0.uv.x;
    let u20 = v2.uv.x - v0.uv.x;
    let v10 = v1.uv.y - v0.uv.y;
    let v20 = v2.uv.y - v0.uv.y;*/
    let z10 = v1.pos.z - v0.pos.z;
    let z20 = v2.pos.z - v0.pos.z;
   
    // Edge function for v0v1
    // (v0y-v1y)px + (v1x-v0x)py + (v0v1y - v0yv1x)
    //   A             B            C
    // A, B & C are constants

    // -1 turns >= 0 test into > 0 
    let bias0 = if is_edge_top_left(dx10, dy01) { 0 } else { -1 };
    let bias1 = if is_edge_top_left(dx21, dy12) { 0 } else { -1 };
    let bias2 = if is_edge_top_left(dx02, dy20) { 0 } else { -1 };
    
    let c0 = x0 * y1 - y0 * x1 + bias0;
    let c1 = x1 * y2 - y1 * x2 + bias1;
    let c2 = x2 * y0 - y2 * x0 + bias2;

    let mut e0_start = dy01 * (minx << 4) + dx10 * (miny << 4) + c0;
    let mut e1_start = dy12 * (minx << 4) + dx21 * (miny << 4) + c1;
    let mut e2_start = dy20 * (minx << 4) + dx02 * (miny << 4) + c2;
    
    let fp_dx10 = dx10 << 4; // A
    let fp_dy01 = dy01 << 4; // B
    
    let fp_dx21 = dx21 << 4; // A
    let fp_dy12 = dy12 << 4; // B
    
    let fp_dx02 = dx02 << 4; // A
    let fp_dy20 = dy20 << 4; // B

    for _ty in miny..maxy {
        let mut e0x = e0_start;
        let mut e1x = e1_start;
        let mut e2x = e2_start;
        for tx in minx..maxx {
            if e0x | e1x | e2x >= 0 {
                let w0 = (e0x - bias0) as f32 * inv_tri_a2;
                //let w1 = (e1x - bias1) as f32 * inv_tri_a2;
                let w2 = (e2x - bias2) as f32 * inv_tri_a2;

                let pixel_offset = fb_offset + (tx as usize);

                let pz = v0.pos.z + z10 * w2 + z20 * w0;
                unsafe {
                    let d = *depth_buffer.add(pixel_offset);
                    if d < pz {
                        *depth_buffer.add(pixel_offset) = pz;
                        *buffer.add(pixel_offset) = 0xFF000000 | (r << 16) | (g << 8) | b;
                    }
                }
            }

            e0x += fp_dy01;
            e1x += fp_dy12;
            e2x += fp_dy20;
        }
        e0_start += fp_dx10;
        e1_start += fp_dx21;
        e2_start += fp_dx02;
        fb_offset += RESOLUTION;
    }
}

fn clear_buffer(buffer: &mut [u32]) {
    for pixel in buffer.iter_mut().take(RESOLUTION*RESOLUTION) {
        *pixel = 0;
    }
}

fn transform_vert_chunk(
    model_verts: &[Vertex],
    xformed_verts: &mut [Vertex],
    world_to_vp: &Matrix4,
    base_index: usize) {

    for (i, xvert) in xformed_verts.iter_mut().enumerate() {
        let j = base_index + i;

        let v4 = transform_point4(&model_verts[j].pos, world_to_vp);
        xvert.pos.x = v4.x / v4.w;
        xvert.pos.y = v4.y / v4.w;
        xvert.pos.z = v4.z / v4.w;

        //xformed_verts[i].uv.x = model_verts[j].normal.x * 256.0 + 255.0;
        //xformed_verts[i].uv.y = model_verts[j].normal.y * 256.0 + 255.0;
    }
}

fn update_blob_positions(blobs : &mut [Blob], angle_degrees : f32) {
    let cos_angle = angle_degrees.to_radians().cos();
    let sin_angle = angle_degrees.to_radians().sin();
    let cx = cos_angle * 50.0;
    let cy = sin_angle * 65.0;

    for (b, blob) in blobs.iter_mut().enumerate() {
        if b == 0 {
            blob.center.x = cx;
            blob.center.y = cy;
        } else if b == 1 {
            blob.center.x = cx;
            blob.center.z = cy;
        } else if b == 2 {
            blob.center.y = cx;
            blob.center.x = cy;
        }
        else {
            blob.center.x = cy;
            blob.center.z = cx;
        }
        blob.center = blob.center * (1.0 / blob.radius);
    }
}

fn draw_box(buffer : &mut [u32], x0 : usize, y0 : usize, color : u32, width : usize) {
    let mut pixel_offset = y0 * RESOLUTION;
    for _y in y0..y0 + 10 {
        for x in x0..x0 + width {
            buffer[pixel_offset + x] = color;
        }
        pixel_offset += RESOLUTION;
    }
}
fn draw_bar(buffer : &mut[u32], width : usize, y : usize, color : u32) {
    let num_boxes = width / 10;
    let mut x = 0;
    for _b in 0..num_boxes {
        draw_box(buffer, x, y, color, 10);
        x += 12;
    }
    let rem_box = width % 10;
    if rem_box != 0 {
        draw_box(buffer, x, y, color, rem_box);
    }
}

fn delta_millis(start_time : &std::time::Instant) -> u32 {
    let time_taken = Instant::now().duration_since(*start_time);

    (time_taken.as_secs() * 1000) as u32 + time_taken.subsec_millis()
}
 
fn classify_triangles(verts : &[Vertex], tris : &[Triangle], tiles : &mut Vec<ScreenTile>) {
    let clamp = |x : i32, lo, hi| {
        if x < lo { lo } else if x > hi { hi } else { x }
    };
    tiles.iter_mut().for_each(|tile| tile.triangles.clear());
    for (tri_index, tri) in tris.iter().enumerate() {
        let v0 = verts[tri.v0];
        let v1 = verts[tri.v1];
        let v2 = verts[tri.v2];

        let x0 = as_fixed_pt(v0.pos.x);
        let y0 = as_fixed_pt(v0.pos.y);
        let x1 = as_fixed_pt(v1.pos.x);
        let y1 = as_fixed_pt(v1.pos.y);
        let x2 = as_fixed_pt(v2.pos.x);
        let y2 = as_fixed_pt(v2.pos.y);
    
        let (mut minx, mut miny) = minxy((x0, y0), (x1, y1), (x2, y2));
        let (mut maxx, mut maxy) = maxxy((x0, y0), (x1, y1), (x2, y2));      
        
        minx >>= TILE_DIM_SHIFT;
        miny >>= TILE_DIM_SHIFT;
        maxx >>= TILE_DIM_SHIFT;
        maxy >>= TILE_DIM_SHIFT;
        minx = clamp(minx, 0, TILES_PER_LINE as i32 - 1);
        miny = clamp(miny, 0, TILES_PER_LINE as i32 - 1);
        maxx = clamp(maxx, 0, TILES_PER_LINE as i32 - 1);
        maxy = clamp(maxy, 0, TILES_PER_LINE as i32 - 1);

        for ty in miny..=maxy {
            for tx in minx..=maxx {
                tiles[tx as usize + ty as usize * TILES_PER_LINE].triangles.push(tri_index);
            }
        }
    }
}

//fn calc_triangle_colors()

fn main() {
    //let img = image::open(&Path::new("phong_1.jpg")).ok().expect("Opening image failed");
    //let imgRGBA = img.as_rgb8().unwrap();
    //let texturePixels = imgRGBA.clone().into_raw();
    
    let cmd_line_args: Vec<String> = env::args().collect();
    println!("{:?}", cmd_line_args);
    let file_name = if cmd_line_args.len() <= 1 {
        String::from("bun_zipper.ply")
    } else {
        cmd_line_args[1].clone()
    };

    let do_metaballs : bool = file_name == "blobs";
    
    let mut verts_world : Vec<Vertex> = vec![];
    let mut faces : Vec<Triangle> = vec![];
    let def_tri = Triangle::default();
    if !do_metaballs {
        //let (verts_world, faces) = load_ply(&file_name);
    }

    let mut framebuffer: Vec<u32> = vec![0; RESOLUTION * RESOLUTION];
    let mut depthbuffer: Vec<f32> = vec![1.0; RESOLUTION * RESOLUTION];

     let mut tiles = Vec::new();
    let tile_rows = (RESOLUTION + TILE_DIM - 1) / TILE_DIM;
    for ty in 0..tile_rows {
        for tx in 0..tile_rows {
            tiles.push(ScreenTile {
                min_x : tx * TILE_DIM,
                min_y : ty * TILE_DIM,
                max_x : cmp::min(tx * TILE_DIM + TILE_DIM, RESOLUTION),
                max_y : cmp::min(ty * TILE_DIM + TILE_DIM, RESOLUTION),
                triangles : Vec::with_capacity(512) 
            });
        }
    }

    let mut window = Window::new(
        "rustrast - ESC to exit",
        RESOLUTION,
        RESOLUTION,
        WindowOptions::default(),
    )
    .unwrap_or_else(|e| {
        panic!("{}", e);
    });

    let mut grid = Grid {
        cells: vec![],
        verts: vec![],
        res: 64
    };
    build_grid(&mut grid);
    let mut blobs = [
        Blob {
            center: Vector3::new(0.0, 0.0, 0.0),
            radius: 40.0,
        },
        Blob {
            center: Vector3::new(20.0, 0.0, 0.0),
            radius: 30.0,
        },
        Blob {
            center: Vector3::new(0.0, 20.0, 0.0),
            radius: 20.0,
        },
        Blob {
            center: Vector3::new(0.0, 20.0, 0.0),
            radius: 10.0,
        },        
    ];

    let iso_level = 0.1;
   
    let mut xformed_verts: Vec<Vertex> = vec![Vertex::default(); verts_world.len()];

    let proj_matrix = perspective_projection_matrix(45.0, 1.0, 0.1, 1000.0);
    let vp_matrix = viewport_matrix(RESOLUTION as Rfloat, RESOLUTION as Rfloat);
    let vpm = view_matrix(1100.0) * proj_matrix * vp_matrix;
    let mut angle = 0.0_f32;
    let mut prev_fps = 0.0_f64;
  
    let mut shading_enabled = false;

    let mut max_verts = 0;
    let mut max_faces = 0;

    // NOTE: This is very handwavy and fairly conservative.
    // It's so that we can fill the vertex table from multiple threads.
    // We first resize our vector to the "maximum expected size", fill it in, then shrink.
    // It's all "unsafe" code, so if we ever exceed our guesstimate, it crashes with an access violation.
    // There must be a better way, but could not find an easy method to convince Rayon to produce from
    // multiple threads (other than using a whole bunch of mutexes/arcs)
    let expected_max_tris = (grid.res*grid.res*grid.res)/3;

    let win_min = Point2 { x : 0, y : 0 };
    let win_max = Point2 { x : RESOLUTION as i32, y : RESOLUTION as i32 };
    while window.is_open() && !window.is_key_down(Key::Escape) {

        let start_time = Instant::now();

        clear_buffer(framebuffer.as_mut_slice());
        for depth in &mut depthbuffer {
            *depth = 1.0;
        }

        update_blob_positions(&mut blobs, angle);

        let rot = rotx_matrix(angle*0.8) * roty_matrix(angle*0.2) * rotz_matrix(angle*0.3);
        let world_to_vp = rot * vpm;

        update_blobs(&mut grid, &blobs);
        let time_blobs = delta_millis(&start_time);

        verts_world.resize(expected_max_tris*3, Vertex::default());
        faces.resize(expected_max_tris, def_tri);

        calc_blob_mesh(&grid, iso_level, &mut verts_world, &mut faces);

        max_verts = cmp::max(max_verts, verts_world.len());
        max_faces = cmp::max(max_faces, faces.len());
        xformed_verts.resize(verts_world.len(), Vertex::default());
        let time_grid = delta_millis(&start_time);
        //println!("Num verts {}", cube_verts.len());
        const VERT_XFORM_CHUNK_SIZE: usize = 512;
        xformed_verts
            .par_chunks_mut(VERT_XFORM_CHUNK_SIZE)
            .enumerate()
            .for_each(|(i, chunk)| {
                transform_vert_chunk(&verts_world, chunk, &world_to_vp, i * VERT_XFORM_CHUNK_SIZE);
            });
        let time_xform = delta_millis(&start_time);

        let light_dir = Vector3::new(0.0, 0.0, 1.0);
        calc_triangle_colors(&mut faces, &verts_world, shading_enabled, light_dir);

        classify_triangles(&xformed_verts, &faces, &mut tiles);
        let fb_slice = UnsafeSlice { ptr : framebuffer.as_mut_ptr(), size : AtomicUsize::new(0) };
        let depth_slice = UnsafeSlice { ptr : depthbuffer.as_mut_ptr(), size : AtomicUsize::new(0) };
        tiles.par_chunks(1).for_each(|chunk| {
            for tile in chunk {
                for index in &tile.triangles {
                    let t = faces[*index];
                    draw_triangle(
                        &xformed_verts[t.v0],
                        &xformed_verts[t.v1],
                        &xformed_verts[t.v2],
                        t.color.x as u32,
                        t.color.y as u32,
                        t.color.z as u32,
                        &win_min, &win_max,
                        fb_slice.ptr,
                        depth_slice.ptr);                 
                }
            }
        });

        let time_draw = delta_millis(&start_time);

        draw_bar(framebuffer.as_mut_slice(), time_blobs as usize, 0, 0xFFFFFFFF);
        draw_bar(framebuffer.as_mut_slice(), time_grid as usize, 12, 0xFFFF0000);
        draw_bar(framebuffer.as_mut_slice(), time_xform as usize, 24, 0xFF00FF00);
        draw_bar(framebuffer.as_mut_slice(), time_draw as usize, 36, 0xFF0000FF);

        let time_taken = Instant::now().duration_since(start_time);
        let time_taken_dbl = time_taken.as_secs() as f64 + time_taken.subsec_nanos() as f64 * 1e-9;
        let fps = 1.0 / time_taken_dbl;
        let smooth_fps = fps * 0.1 + prev_fps * 0.9;
        prev_fps = smooth_fps;
        window.set_title(&format!("FPS {} Grid res {}", smooth_fps as u32, grid.res));

        window.update_with_buffer(framebuffer.as_slice(), RESOLUTION, RESOLUTION).unwrap();

        angle += time_taken_dbl as f32 * 50.0;

        if window.is_key_down(Key::Space) {
            shading_enabled = !shading_enabled;
        }
    }
    //write_tga(&Path::new("triangle.tga"), framebuffer.as_slice(), RESOLUTION, RESOLUTION);
    println!("{:?} {:?}", max_verts, max_faces);
}

fn calc_triangle_colors(faces: &mut Vec<Triangle>, verts_world: &[Vertex], shading_enabled: bool, light_dir: Vector3) {
    let clamp0 = |x : Rfloat| { if x >= 0.0 { x } else { 0.0 }};    
    for t in faces {
        let n = triangle_normal(
            &verts_world[t.v0].pos,
            &verts_world[t.v1].pos,
            &verts_world[t.v2].pos,
        );
        let diffuse : Rfloat = if shading_enabled { clamp0(dot(&light_dir, &n)) } else { 1.0 };
        t.color.x = diffuse * ((n.x + 1.0) * 0.5) * 255.0;
        t.color.y = diffuse * ((n.y + 1.0) * 0.5) * 255.0;
        t.color.z = diffuse * ((n.z + 1.0) * 0.5) * 255.0;
    }
}
