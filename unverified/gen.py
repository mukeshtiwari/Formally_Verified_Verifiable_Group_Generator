from Crypto.Hash import SHA256
import time


P = 0xff600483db6abfc5b45eab78594b3533d550d9f1bf2a992a7a8daa6dc34f8045ad4e6e0c429d334eeeaaefd7e23d4810be00e4cc1492cba325ba81ff2d5a5b305a8d17eb3bf4a06a349d392e00d329744a5179380344e82a18c47933438f891e22aeef812d69c8f75e326cb70ea000c3f776dfdbd604638c2ef717fc26d02e17
Q = 0xe21e04f911d1ed7991008ecaab3bf775984309c3
domain_parameter_seed = b'180180ee2f0ae4a7b3a1ab1b8414228913ef2911'
ggen = b'6767656e'
index = b'79'
G = 0xc52a4a0ff3b7e61fdf1867ce84138369a6154f4afa92966e3c827e25cfa6cf508b90e5de419e1337e07a2e9e2a3cd5dea704d175f8ebf6af397d69e110b96afb17c7a03259329e4829b0d03bbc7896b15b4ade53e130858cc34d96269aa89041f409136c7242a38895c9d5bccad4f389af1d7a4bd1398bd072dffa896233397a



def compute_gen():
    k = (P - 1) // Q
    for count in range(1, 0xffff):
        U = bytes.fromhex((domain_parameter_seed + ggen + index).decode('utf8')) + count.to_bytes(2, 'big')
        W = int.from_bytes(SHA256.new(U).digest(), 'big')
        g = pow(W, k, P)
        print(g)
        if g != 1:
            break

    return g

if __name__ == "__main__":
    ts = time.time()
    g = compute_gen()
    te = time.time()
    print(g == G)
    print(te - ts)
