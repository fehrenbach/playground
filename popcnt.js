// First, write the web assembly program, in the web assembly AST.
// Mine looks like this:

/* ;; popcnt.wat
(module
  (func (export "popcnt") (param i32) (result i32)
    (i32.popcnt (get_local 0))))
*/

// Then compile it to binary. There's a command line tool. There's
// also a demo webpage, that's what I used.
// https://webassembly.github.io/wabt/demo/wat2wasm/

// The result is a wasm file, which is just 55 bytes long. I don't
// want to host it somewhere, then have the browser load it and
// whatnot, so I opened it in emacs, M-x hexl-mode, copy & paste and
// massage it a bit into a Uint8Array.

// Fun fact: this sequence 70 6f 70 63 6e 74 on the second line spells
// the name of the exported function: popcnt

var bytes = Uint8Array.from([0x00,0x61,0x73,0x6d,0x01,0x00,0x00,0x00,0x01,0x06,0x01,0x60,0x01,0x7f,0x01,0x7f,
                             0x03,0x02,0x01,0x00,0x07,0x0a,0x01,0x06,0x70,0x6f,0x70,0x63,0x6e,0x74,0x00,0x00,
                             0x0a,0x07,0x01,0x05,0x00,0x20,0x00,0x69,0x0b,0x00,0x0c,0x04,0x6e,0x61,0x6d,0x65,
                             0x02,0x05,0x01,0x00,0x01,0x00,0x00]);

// The common JavaScript implementation of popcount, for comparison.

function popcount (n) {
    n = n - ((n >> 1) & 0x55555555);
    n = (n & 0x33333333) + ((n >> 2) & 0x33333333);
    return ((n + (n >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
}

// WebAssembly can combile things from a byte array, but produces a
// Promise. This is a bit annoying, because apparently there is no way
// to wait synchronously on a promise being fulfilled. I'm not sure
// whether that even makes sence, since JS is single threaded. But
// anyway, it's annoying, because now everything is in a callback.
WebAssembly.instantiate(bytes,{}).then(function (webassemblythingy) {
    // "instantiating" WebAssembly with our bytes produces something.
    // That something has an instance with exports and finally our
    // popcnt function!
    var popcnt = webassemblythingy.instance.exports.popcnt;

    // Now let's run it.
    var count = 1000000;
    var res = 0;
    console.time("wasm");
    for (var i = 0; i < count; i++)
        res += popcnt(i);
    console.timeEnd("wasm");
    console.log(res);

    // Let's run the JS version for comparison.
    res = 0;
    console.time("js");
    for (var j = 0; j < count; j++)
        res += popcount(j);
    console.timeEnd("js");
    console.log(res);

    // They are both extremely fast. On Firefox 62.0.2 (October 2018)
    // on my fairly old laptop I get the following for 1000000 calls:
    /* 
       wasm: 17ms
       9884992 
       js: 306ms
       9884992
    */

    // On nodejs v10.11.0 I get the following for 1000000 calls:
    /* 
       wasm: 17.885ms
       9884992
       js: 7.334ms
       9884992
    */

    // Chromium 69.0.3497.100 has quite variable performance, this is
    // about the best I can get for 1000000 calls:
    /* 
       wasm: 19.220703125ms
       9884992
       js: 7.992919921875ms
       9884992
    */

    // Firefox 63.0.0 improves to ~7-8ms WASM but stays at ~300ms JS
});
