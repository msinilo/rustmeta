# rustmeta
Metaballs (blobs) coded in Rust. 100% software rendering. It is basically a Rust version of my old demo effect from the 90s (back then we'd use a fake Phong shading, though).
Metaballs tables/original C code from Paul Bourke - http://www.paulbourke.net/geometry/polygonise/
https://github.com/blitzcode/rust-exp was a great learning source.
Blob generation/vertex transformation & rasterization is all parallelizd with Rayon, but not super safe (especially blob generation), could not find a good way to use Rayon as a "producer".

![Video](video.gif "Short video")

Press SPACE to enabled/disable lighting.
