global.fetch = require('node-fetch');
const { Headers, Request, Response } = fetch;

let imports = {};
imports['__wbindgen_placeholder__'] = module.exports;
let wasm;
const { Buffer } = require(String.raw`buffer`);
const { spawn } = require(String.raw`child_process`);
const { access, mkdir, readdir, readFile, readlink, stat, unlink, unlinkSync, writeFile, writeFileSync } = require(String.raw`fs`);
const { getPassword, setPassword, deletePassword, findCredentials } = require(String.raw`keytar`);
const { homedir, tmpdir } = require(String.raw`os`);
const { basename, delimiter, dirname, extname, join, normalize, relative } = require(String.raw`path`);
const { arch, env, hrtime, platform } = require(String.raw`process`);
const { Readable } = require(String.raw`stream`);
const { setTimeout } = require(String.raw`timers`);
const { TextDecoder, TextEncoder } = require(String.raw`util`);
const { Uri, Position, Selection, Range, commands, env: env2, window: window2, workspace } = require(String.raw`vscode`);

let cachedTextDecoder = new TextDecoder('utf-8', { ignoreBOM: true, fatal: true });

cachedTextDecoder.decode();

let cachegetUint8Memory0 = null;
function getUint8Memory0() {
    if (cachegetUint8Memory0 === null || cachegetUint8Memory0.buffer !== wasm.memory.buffer) {
        cachegetUint8Memory0 = new Uint8Array(wasm.memory.buffer);
    }
    return cachegetUint8Memory0;
}

function getStringFromWasm0(ptr, len) {
    return cachedTextDecoder.decode(getUint8Memory0().subarray(ptr, ptr + len));
}

const heap = new Array(32).fill(undefined);

heap.push(undefined, null, true, false);

let heap_next = heap.length;

function addHeapObject(obj) {
    if (heap_next === heap.length) heap.push(heap.length + 1);
    const idx = heap_next;
    heap_next = heap[idx];

    heap[idx] = obj;
    return idx;
}

function getObject(idx) { return heap[idx]; }

let WASM_VECTOR_LEN = 0;

let cachedTextEncoder = new TextEncoder('utf-8');

const encodeString = (typeof cachedTextEncoder.encodeInto === 'function'
    ? function (arg, view) {
    return cachedTextEncoder.encodeInto(arg, view);
}
    : function (arg, view) {
    const buf = cachedTextEncoder.encode(arg);
    view.set(buf);
    return {
        read: arg.length,
        written: buf.length
    };
});

function passStringToWasm0(arg, malloc, realloc) {

    if (realloc === undefined) {
        const buf = cachedTextEncoder.encode(arg);
        const ptr = malloc(buf.length);
        getUint8Memory0().subarray(ptr, ptr + buf.length).set(buf);
        WASM_VECTOR_LEN = buf.length;
        return ptr;
    }

    let len = arg.length;
    let ptr = malloc(len);

    const mem = getUint8Memory0();

    let offset = 0;

    for (; offset < len; offset++) {
        const code = arg.charCodeAt(offset);
        if (code > 0x7F) break;
        mem[ptr + offset] = code;
    }

    if (offset !== len) {
        if (offset !== 0) {
            arg = arg.slice(offset);
        }
        ptr = realloc(ptr, len, len = offset + arg.length * 3);
        const view = getUint8Memory0().subarray(ptr + offset, ptr + len);
        const ret = encodeString(arg, view);

        offset += ret.written;
    }

    WASM_VECTOR_LEN = offset;
    return ptr;
}

let cachegetInt32Memory0 = null;
function getInt32Memory0() {
    if (cachegetInt32Memory0 === null || cachegetInt32Memory0.buffer !== wasm.memory.buffer) {
        cachegetInt32Memory0 = new Int32Array(wasm.memory.buffer);
    }
    return cachegetInt32Memory0;
}

function dropObject(idx) {
    if (idx < 36) return;
    heap[idx] = heap_next;
    heap_next = idx;
}

function takeObject(idx) {
    const ret = getObject(idx);
    dropObject(idx);
    return ret;
}

function isLikeNone(x) {
    return x === undefined || x === null;
}

let cachegetFloat64Memory0 = null;
function getFloat64Memory0() {
    if (cachegetFloat64Memory0 === null || cachegetFloat64Memory0.buffer !== wasm.memory.buffer) {
        cachegetFloat64Memory0 = new Float64Array(wasm.memory.buffer);
    }
    return cachegetFloat64Memory0;
}

function debugString(val) {
    // primitive types
    const type = typeof val;
    if (type == 'number' || type == 'boolean' || val == null) {
        return  `${val}`;
    }
    if (type == 'string') {
        return `"${val}"`;
    }
    if (type == 'symbol') {
        const description = val.description;
        if (description == null) {
            return 'Symbol';
        } else {
            return `Symbol(${description})`;
        }
    }
    if (type == 'function') {
        const name = val.name;
        if (typeof name == 'string' && name.length > 0) {
            return `Function(${name})`;
        } else {
            return 'Function';
        }
    }
    // objects
    if (Array.isArray(val)) {
        const length = val.length;
        let debug = '[';
        if (length > 0) {
            debug += debugString(val[0]);
        }
        for(let i = 1; i < length; i++) {
            debug += ', ' + debugString(val[i]);
        }
        debug += ']';
        return debug;
    }
    // Test for built-in
    const builtInMatches = /\[object ([^\]]+)\]/.exec(toString.call(val));
    let className;
    if (builtInMatches.length > 1) {
        className = builtInMatches[1];
    } else {
        // Failed to match the standard '[object ClassName]'
        return toString.call(val);
    }
    if (className == 'Object') {
        // we're a user defined class or Object
        // JSON.stringify avoids problems with cycles, and is generally much
        // easier than looping through ownProperties of `val`.
        try {
            return 'Object(' + JSON.stringify(val) + ')';
        } catch (_) {
            return 'Object';
        }
    }
    // errors
    if (val instanceof Error) {
        return `${val.name}: ${val.message}\n${val.stack}`;
    }
    // TODO we could test for more things here, like `Set`s and `Map`s.
    return className;
}

function makeMutClosure(arg0, arg1, dtor, f) {
    const state = { a: arg0, b: arg1, cnt: 1, dtor };
    const real = (...args) => {
        // First up with a closure we increment the internal reference
        // count. This ensures that the Rust closure environment won't
        // be deallocated while we're invoking it.
        state.cnt++;
        const a = state.a;
        state.a = 0;
        try {
            return f(a, state.b, ...args);
        } finally {
            if (--state.cnt === 0) {
                wasm.__wbindgen_export_2.get(state.dtor)(a, state.b);

            } else {
                state.a = a;
            }
        }
    };
    real.original = state;

    return real;
}
function __wbg_adapter_34(arg0, arg1, arg2, arg3) {
    wasm._dyn_core__ops__function__FnMut__A_B___Output___R_as_wasm_bindgen__closure__WasmClosure___describe__invoke__hf9fe6f84875fb2fa(arg0, arg1, addHeapObject(arg2), addHeapObject(arg3));
}

let stack_pointer = 32;

function addBorrowedObject(obj) {
    if (stack_pointer == 1) throw new Error('out of js stack');
    heap[--stack_pointer] = obj;
    return stack_pointer;
}
function __wbg_adapter_37(arg0, arg1, arg2) {
    try {
        wasm._dyn_core__ops__function__FnMut___A____Output___R_as_wasm_bindgen__closure__WasmClosure___describe__invoke__h43158d47be0e7eca(arg0, arg1, addBorrowedObject(arg2));
    } finally {
        heap[stack_pointer++] = undefined;
    }
}

function __wbg_adapter_40(arg0, arg1, arg2) {
    wasm._dyn_core__ops__function__FnMut__A____Output___R_as_wasm_bindgen__closure__WasmClosure___describe__invoke__h49ac35225d542fd0(arg0, arg1, addHeapObject(arg2));
}

function __wbg_adapter_43(arg0, arg1) {
    wasm._dyn_core__ops__function__FnMut_____Output___R_as_wasm_bindgen__closure__WasmClosure___describe__invoke__h5c13abb9cda48739(arg0, arg1);
}

function __wbg_adapter_46(arg0, arg1, arg2, arg3) {
    var ret = wasm._dyn_core__ops__function__FnMut__A_B___Output___R_as_wasm_bindgen__closure__WasmClosure___describe__invoke__h5ddcd33cf977719d(arg0, arg1, addHeapObject(arg2), addHeapObject(arg3));
    return takeObject(ret);
}

function __wbg_adapter_49(arg0, arg1, arg2) {
    wasm._dyn_core__ops__function__FnMut__A____Output___R_as_wasm_bindgen__closure__WasmClosure___describe__invoke__h58a47329ce3e8c4e(arg0, arg1, addHeapObject(arg2));
}

/**
* @param {string} path
*/
module.exports.internal_generate_package_json = function(path) {
    var ptr0 = passStringToWasm0(path, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    wasm.internal_generate_package_json(ptr0, len0);
};

/**
* @param {any} ctx
*/
module.exports.activate = function(ctx) {
    try {
        wasm.activate(addBorrowedObject(ctx));
    } finally {
        heap[stack_pointer++] = undefined;
    }
};

/**
* @returns {any}
*/
module.exports.deactivate = function() {
    var ret = wasm.deactivate();
    return takeObject(ret);
};

function handleError(f) {
    return function () {
        try {
            return f.apply(this, arguments);

        } catch (e) {
            wasm.__wbindgen_exn_store(addHeapObject(e));
        }
    };
}

let cachegetUint32Memory0 = null;
function getUint32Memory0() {
    if (cachegetUint32Memory0 === null || cachegetUint32Memory0.buffer !== wasm.memory.buffer) {
        cachegetUint32Memory0 = new Uint32Array(wasm.memory.buffer);
    }
    return cachegetUint32Memory0;
}

function getArrayJsValueFromWasm0(ptr, len) {
    const mem = getUint32Memory0();
    const slice = mem.subarray(ptr / 4, ptr / 4 + len);
    const result = [];
    for (let i = 0; i < slice.length; i++) {
        result.push(takeObject(slice[i]));
    }
    return result;
}
function __wbg_adapter_347(arg0, arg1, arg2, arg3) {
    wasm.wasm_bindgen__convert__closures__invoke2_mut__hbd9502004981f6e3(arg0, arg1, addHeapObject(arg2), addHeapObject(arg3));
}

module.exports.__wbindgen_json_parse = function(arg0, arg1) {
    var ret = JSON.parse(getStringFromWasm0(arg0, arg1));
    return addHeapObject(ret);
};

module.exports.__wbindgen_json_serialize = function(arg0, arg1) {
    const obj = getObject(arg1);
    var ret = JSON.stringify(obj === undefined ? null : obj);
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbindgen_is_undefined = function(arg0) {
    var ret = getObject(arg0) === undefined;
    return ret;
};

module.exports.__wbindgen_is_null = function(arg0) {
    var ret = getObject(arg0) === null;
    return ret;
};

module.exports.__wbindgen_object_drop_ref = function(arg0) {
    takeObject(arg0);
};

module.exports.__wbindgen_object_clone_ref = function(arg0) {
    var ret = getObject(arg0);
    return addHeapObject(ret);
};

module.exports.__wbindgen_cb_drop = function(arg0) {
    const obj = takeObject(arg0).original;
    if (obj.cnt-- == 1) {
        obj.a = 0;
        return true;
    }
    var ret = false;
    return ret;
};

module.exports.__wbindgen_string_new = function(arg0, arg1) {
    var ret = getStringFromWasm0(arg0, arg1);
    return addHeapObject(ret);
};

module.exports.__wbg_getPassword_2242989f986b72a7 = function(arg0, arg1, arg2, arg3) {
    var ret = getPassword(getStringFromWasm0(arg0, arg1), getStringFromWasm0(arg2, arg3));
    return addHeapObject(ret);
};

module.exports.__wbg_setPassword_4fda06de4fd2460b = function(arg0, arg1, arg2, arg3, arg4, arg5) {
    var ret = setPassword(getStringFromWasm0(arg0, arg1), getStringFromWasm0(arg2, arg3), getStringFromWasm0(arg4, arg5));
    return addHeapObject(ret);
};

module.exports.__wbg_deletePassword_88010a0f49172f1e = function(arg0, arg1, arg2, arg3) {
    var ret = deletePassword(getStringFromWasm0(arg0, arg1), getStringFromWasm0(arg2, arg3));
    return addHeapObject(ret);
};

module.exports.__wbg_findCredentials_4583163b05d472b1 = function(arg0, arg1) {
    var ret = findCredentials(getStringFromWasm0(arg0, arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_new_83a0b608494484fd = handleError(function() {
    var ret = new Headers();
    return addHeapObject(ret);
});

module.exports.__wbg_append_6363bf15ad177fce = handleError(function(arg0, arg1, arg2, arg3, arg4) {
    getObject(arg0).append(getStringFromWasm0(arg1, arg2), getStringFromWasm0(arg3, arg4));
});

module.exports.__wbg_newwithstrandinit_11debb554792e043 = handleError(function(arg0, arg1, arg2) {
    var ret = new Request(getStringFromWasm0(arg0, arg1), getObject(arg2));
    return addHeapObject(ret);
});

module.exports.__wbg_instanceof_Response_f52c65c389890639 = function(arg0) {
    var ret = getObject(arg0) instanceof Response;
    return ret;
};

module.exports.__wbg_status_f3cb2b4d20a23f59 = function(arg0) {
    var ret = getObject(arg0).status;
    return ret;
};

module.exports.__wbg_headers_6fafb2c7669a8ac5 = function(arg0) {
    var ret = getObject(arg0).headers;
    return addHeapObject(ret);
};

module.exports.__wbg_arrayBuffer_0ba17dfaad804b6f = handleError(function(arg0) {
    var ret = getObject(arg0).arrayBuffer();
    return addHeapObject(ret);
});

module.exports.__wbg_text_afdc7a1dc7edda52 = handleError(function(arg0) {
    var ret = getObject(arg0).text();
    return addHeapObject(ret);
});

module.exports.__wbg_instanceof_Window_49f532f06a9786ee = function(arg0) {
    var ret = true;
    return ret;
};

module.exports.__wbg_fetch_f532e04b8fe49aa0 = function(arg0, arg1) {
    var ret = getObject(arg0).fetch(getObject(arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_from_e1600e15d6948c00 = function(arg0) {
    var ret = Buffer.from(takeObject(arg0));
    return addHeapObject(ret);
};

module.exports.__wbg_buffer_56633580c04cda38 = function(arg0) {
    var ret = getObject(arg0).buffer;
    return addHeapObject(ret);
};

module.exports.__wbg_kill_d557c7de73ea9c49 = function(arg0, arg1) {
    getObject(arg0).kill(arg1);
};

module.exports.__wbg_on_36351aa3b75ec411 = function(arg0, arg1, arg2, arg3) {
    getObject(arg0).on(getStringFromWasm0(arg1, arg2), getObject(arg3));
};

module.exports.__wbg_stdin_c7983f9158382bf8 = function(arg0) {
    var ret = getObject(arg0).stdin;
    return isLikeNone(ret) ? 0 : addHeapObject(ret);
};

module.exports.__wbg_stdout_2fa21a46906ed3a3 = function(arg0) {
    var ret = getObject(arg0).stdout;
    return isLikeNone(ret) ? 0 : addHeapObject(ret);
};

module.exports.__wbg_stderr_3b16e3b0d4edfa23 = function(arg0) {
    var ret = getObject(arg0).stderr;
    return isLikeNone(ret) ? 0 : addHeapObject(ret);
};

module.exports.__wbg_spawn_1c089180cb649098 = function(arg0, arg1, arg2, arg3) {
    var ret = spawn(getStringFromWasm0(arg0, arg1), takeObject(arg2), takeObject(arg3));
    return addHeapObject(ret);
};

module.exports.__wbg_debug_8b3b0e4d8f33463e = function(arg0, arg1) {
    console.debug(getStringFromWasm0(arg0, arg1));
};

module.exports.__wbg_error_b914e066ace0c089 = function(arg0, arg1) {
    console.error(getStringFromWasm0(arg0, arg1));
};

module.exports.__wbg_info_da4b7979c1ee5a0c = function(arg0, arg1) {
    console.info(getStringFromWasm0(arg0, arg1));
};

module.exports.__wbg_log_06b168a15a092deb = function(arg0, arg1) {
    console.log(getStringFromWasm0(arg0, arg1));
};

module.exports.__wbg_warn_417f164c3d7a673d = function(arg0, arg1) {
    console.warn(getStringFromWasm0(arg0, arg1));
};

module.exports.__wbg_access_b546fc6a05efe5cf = function(arg0, arg1, arg2) {
    access(getStringFromWasm0(arg0, arg1), takeObject(arg2));
};

module.exports.__wbg_mkdir_5e58ff5f9b14b0bf = function(arg0, arg1, arg2, arg3) {
    mkdir(getStringFromWasm0(arg0, arg1), takeObject(arg2), takeObject(arg3));
};

module.exports.__wbg_readdir_f5fb82f661749083 = function(arg0, arg1, arg2, arg3) {
    readdir(getStringFromWasm0(arg0, arg1), takeObject(arg2), takeObject(arg3));
};

module.exports.__wbg_readFile_7c46d0323f1e0c6c = function(arg0, arg1, arg2, arg3) {
    readFile(getStringFromWasm0(arg0, arg1), takeObject(arg2), takeObject(arg3));
};

module.exports.__wbg_readlink_69c4f066d56bfe8f = function(arg0, arg1, arg2) {
    readlink(getStringFromWasm0(arg0, arg1), takeObject(arg2));
};

module.exports.__wbg_stat_27d1b7af57e1e7b1 = function(arg0, arg1, arg2, arg3) {
    stat(getStringFromWasm0(arg0, arg1), takeObject(arg2), takeObject(arg3));
};

module.exports.__wbg_unlink_684ebcb1816d82cd = function(arg0, arg1, arg2) {
    unlink(getStringFromWasm0(arg0, arg1), takeObject(arg2));
};

module.exports.__wbg_unlinkSync_1abcb418ea695f16 = function(arg0, arg1) {
    unlinkSync(getStringFromWasm0(arg0, arg1));
};

module.exports.__wbg_writeFile_bd479c8fd5e7b03a = function(arg0, arg1, arg2, arg3, arg4) {
    writeFile(getStringFromWasm0(arg0, arg1), takeObject(arg2), takeObject(arg3), takeObject(arg4));
};

module.exports.__wbg_writeFileSync_c000cd173ee01aa2 = handleError(function(arg0, arg1, arg2, arg3) {
    writeFileSync(getStringFromWasm0(arg0, arg1), getStringFromWasm0(arg2, arg3));
});

module.exports.__wbg_homedir_297332d10cbad21e = function(arg0) {
    var ret = homedir();
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_tmpdir_3dca82c0223946aa = function(arg0) {
    var ret = tmpdir();
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_basename_746b6797c89b6c22 = function(arg0, arg1, arg2) {
    var ret = basename(getStringFromWasm0(arg1, arg2));
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_basename_89e831b704be1840 = function(arg0, arg1, arg2, arg3, arg4) {
    var ret = basename(getStringFromWasm0(arg1, arg2), getStringFromWasm0(arg3, arg4));
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_dirname_9d5b4ae6ecb16b24 = function(arg0, arg1, arg2) {
    var ret = dirname(getStringFromWasm0(arg1, arg2));
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_extname_5d68fc4b18775c73 = function(arg0, arg1, arg2) {
    var ret = extname(getStringFromWasm0(arg1, arg2));
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_join_e2d82d375fd3d5cc = function(arg0, arg1, arg2, arg3, arg4) {
    var ret = join(getStringFromWasm0(arg1, arg2), getStringFromWasm0(arg3, arg4));
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_normalize_05247a076af3ea6f = function(arg0, arg1, arg2) {
    var ret = normalize(getStringFromWasm0(arg1, arg2));
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_relative_ab02a95e2bff2de3 = function(arg0, arg1, arg2, arg3, arg4) {
    var ret = relative(getStringFromWasm0(arg1, arg2), getStringFromWasm0(arg3, arg4));
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_static_accessor_DELIMITER_476956bdb6c4a9d3 = function() {
    var ret = delimiter;
    return addHeapObject(ret);
};

module.exports.__wbg_hrtime_c9b72aac41dc820f = function() {
    var ret = hrtime();
    return addHeapObject(ret);
};

module.exports.__wbg_static_accessor_ARCH_4cb410e1ed8f8e77 = function(arg0) {
    var ret = arch;
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_static_accessor_ENV_8057540a23828e16 = function() {
    var ret = env;
    return addHeapObject(ret);
};

module.exports.__wbg_static_accessor_PLATFORM_32f2e67c1100e8ca = function(arg0) {
    var ret = platform;
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_instanceof_Readable_4459bbecf5447d03 = function(arg0) {
    var ret = getObject(arg0) instanceof Readable;
    return ret;
};

module.exports.__wbg_on_583636a922c06539 = function(arg0, arg1, arg2, arg3) {
    getObject(arg0).on(getStringFromWasm0(arg1, arg2), getObject(arg3));
};

module.exports.__wbg_read_b459d2644a5a0f09 = function(arg0) {
    var ret = getObject(arg0).read();
    return isLikeNone(ret) ? 0 : addHeapObject(ret);
};

module.exports.__wbg_end_36a0401e8af709ca = handleError(function(arg0, arg1, arg2) {
    getObject(arg0).end(getObject(arg1), takeObject(arg2));
});

module.exports.__wbg_setTimeout_a533d4acc9191bca = function(arg0, arg1) {
    setTimeout(takeObject(arg0), arg1);
};

module.exports.__wbg_file_711f26108aabfdc9 = function(arg0, arg1) {
    var ret = Uri.file(getStringFromWasm0(arg0, arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_fsPath_803cbd07af67fd69 = function(arg0, arg1) {
    var ret = getObject(arg1).fsPath;
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_parse_e01b70039d02a4a4 = function(arg0, arg1, arg2) {
    var ret = Uri.parse(getStringFromWasm0(arg0, arg1), arg2 !== 0);
    return addHeapObject(ret);
};

module.exports.__wbg_extensionPath_971f4f484b319768 = function(arg0, arg1) {
    var ret = getObject(arg1).extensionPath;
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_globalState_b28a0fffed78bd51 = function(arg0) {
    var ret = getObject(arg0).globalState;
    return addHeapObject(ret);
};

module.exports.__wbg_append_d9a5e05ff7fb4d1f = function(arg0, arg1, arg2) {
    getObject(arg0).append(getStringFromWasm0(arg1, arg2));
};

module.exports.__wbg_clear_f784be7184bf030b = function(arg0) {
    getObject(arg0).clear();
};

module.exports.__wbg_hide_86da04d5393020f0 = function(arg0) {
    getObject(arg0).hide();
};

module.exports.__wbg_show_d6e00f82e8cb19a2 = function(arg0, arg1) {
    getObject(arg0).show(arg1 !== 0);
};

module.exports.__wbg_workspaceState_a3572be00dae53fc = function(arg0) {
    var ret = getObject(arg0).workspaceState;
    return addHeapObject(ret);
};

module.exports.__wbg_active_9e6a519991fb5692 = function(arg0) {
    var ret = getObject(arg0).active;
    return ret;
};

module.exports.__wbg_dispose_45c0b697ca37872c = function(arg0) {
    getObject(arg0).dispose();
};

module.exports.__wbg_onDidDispose_73c499b1f1cd30f9 = function(arg0, arg1) {
    getObject(arg0).onDidDispose(takeObject(arg1));
};

module.exports.__wbg_reveal_3f4e3ebe10ac2e1a = function(arg0, arg1, arg2) {
    getObject(arg0).reveal(arg1, arg2 !== 0);
};

module.exports.__wbg_webview_59d36352aa3f90e9 = function(arg0) {
    var ret = getObject(arg0).webview;
    return addHeapObject(ret);
};

module.exports.__wbg_onDidReceiveMessage_571b507e6b28338e = function(arg0, arg1) {
    getObject(arg0).onDidReceiveMessage(getObject(arg1));
};

module.exports.__wbg_postMessage_6b17fe32acc19355 = function(arg0, arg1) {
    var ret = getObject(arg0).postMessage(takeObject(arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_sethtml_57368d4662ba3180 = function(arg0, arg1, arg2) {
    getObject(arg0).html = getStringFromWasm0(arg1, arg2);
};

module.exports.__wbg_fileName_664cc60d52b49e54 = function(arg0, arg1) {
    var ret = getObject(arg1).fileName;
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_getText_4575d3b30e6ff577 = function(arg0, arg1) {
    var ret = getObject(arg1).getText();
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbg_edit_287ed4c37dd28aea = function(arg0, arg1) {
    var ret = getObject(arg0).edit(getObject(arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_document_d796d64a3b4c3b4b = function(arg0) {
    var ret = getObject(arg0).document;
    return addHeapObject(ret);
};

module.exports.__wbg_revealRange_c9bae007ae897b37 = function(arg0, arg1, arg2) {
    getObject(arg0).revealRange(getObject(arg1), arg2);
};

module.exports.__wbg_setselection_942daa2ad465e5a5 = function(arg0, arg1) {
    getObject(arg0).selection = takeObject(arg1);
};

module.exports.__wbg_insert_dfafd19f91ede4d0 = function(arg0, arg1, arg2, arg3) {
    getObject(arg0).insert(getObject(arg1), getStringFromWasm0(arg2, arg3));
};

module.exports.__wbg_new_3e5dc7b91ab8d7bc = function(arg0, arg1) {
    var ret = new Position(arg0 >>> 0, arg1 >>> 0);
    return addHeapObject(ret);
};

module.exports.__wbg_new_b2d3834849db711f = function(arg0, arg1) {
    var ret = new Selection(getObject(arg0), getObject(arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_new_13b597da17edc87b = function(arg0, arg1) {
    var ret = new Range(getObject(arg0), getObject(arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_sendText_e96e085fee63fdeb = function(arg0, arg1, arg2, arg3) {
    getObject(arg0).sendText(getStringFromWasm0(arg1, arg2), arg3 === 0xFFFFFF ? undefined : arg3 !== 0);
};

module.exports.__wbg_show_e8184f7237205b83 = function(arg0, arg1) {
    getObject(arg0).show(arg1 === 0xFFFFFF ? undefined : arg1 !== 0);
};

module.exports.__wbg_get_bb8c31cd44761a4c = function(arg0, arg1, arg2) {
    var ret = getObject(arg0).get(getStringFromWasm0(arg1, arg2));
    return addHeapObject(ret);
};

module.exports.__wbg_update_d3698b2247cd265f = function(arg0, arg1, arg2, arg3) {
    var ret = getObject(arg0).update(getStringFromWasm0(arg1, arg2), getObject(arg3));
    return addHeapObject(ret);
};

module.exports.__wbg_hide_22b19bb9122460f6 = function(arg0) {
    getObject(arg0).hide();
};

module.exports.__wbg_settext_fd0f22fc350fbfa3 = function(arg0, arg1, arg2) {
    getObject(arg0).text = getStringFromWasm0(arg1, arg2);
};

module.exports.__wbg_show_877a4431ce8b2c51 = function(arg0) {
    getObject(arg0).show();
};

module.exports.__wbg_report_aea0cf3bf389cd3a = function(arg0, arg1) {
    getObject(arg0).report(takeObject(arg1));
};

module.exports.__wbg_onCancellationRequested_eacbd4229a8b3ef9 = function(arg0) {
    var ret = getObject(arg0).onCancellationRequested;
    return addHeapObject(ret);
};

module.exports.__wbg_get_b7b0f344c449b7f2 = function(arg0, arg1, arg2) {
    var ret = getObject(arg0).get(getStringFromWasm0(arg1, arg2));
    return addHeapObject(ret);
};

module.exports.__wbg_update_4978c631d7e11f7b = function(arg0, arg1, arg2, arg3, arg4) {
    var ret = getObject(arg0).update(getStringFromWasm0(arg1, arg2), getObject(arg3), arg4);
    return addHeapObject(ret);
};

module.exports.__wbg_executeCommand_cf1ff8cd94e6e8ed = function(arg0, arg1, arg2) {
    var ret = commands.executeCommand(getStringFromWasm0(arg0, arg1), ...takeObject(arg2));
    return addHeapObject(ret);
};

module.exports.__wbg_registerCommand_ab1bde1668543bcd = function(arg0, arg1, arg2) {
    commands.registerCommand(getStringFromWasm0(arg0, arg1), getObject(arg2));
};

module.exports.__wbg_openExternal_3b123a2f11286639 = function(arg0) {
    var ret = env2.openExternal(getObject(arg0));
    return addHeapObject(ret);
};

module.exports.__wbg_createOutputChannel_408ab7fff20b3107 = function(arg0, arg1) {
    var ret = window2.createOutputChannel(getStringFromWasm0(arg0, arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_createStatusBarItem_39c15d4a5606ea1e = function() {
    var ret = window2.createStatusBarItem();
    return addHeapObject(ret);
};

module.exports.__wbg_createTerminal_a5946070ea19d5d6 = function(arg0) {
    var ret = window2.createTerminal(takeObject(arg0));
    return addHeapObject(ret);
};

module.exports.__wbg_createWebviewPanel_9be2c02ad0a17caf = function(arg0, arg1, arg2, arg3, arg4, arg5) {
    var ret = window2.createWebviewPanel(getStringFromWasm0(arg0, arg1), getStringFromWasm0(arg2, arg3), takeObject(arg4), takeObject(arg5));
    return addHeapObject(ret);
};

module.exports.__wbg_showErrorMessage_c713b86d9addc8b2 = function(arg0, arg1, arg2, arg3, arg4) {
    var v0 = getArrayJsValueFromWasm0(arg3, arg4).slice();
    wasm.__wbindgen_free(arg3, arg4 * 4);
    var ret = window2.showErrorMessage(getStringFromWasm0(arg0, arg1), getObject(arg2), ...v0);
    return addHeapObject(ret);
};

module.exports.__wbg_showInformationMessage_d97adf70448da4d4 = function(arg0, arg1, arg2, arg3, arg4) {
    var v0 = getArrayJsValueFromWasm0(arg3, arg4).slice();
    wasm.__wbindgen_free(arg3, arg4 * 4);
    var ret = window2.showInformationMessage(getStringFromWasm0(arg0, arg1), getObject(arg2), ...v0);
    return addHeapObject(ret);
};

module.exports.__wbg_showInputBox_fa73f1fd5a25a826 = function(arg0) {
    var ret = window2.showInputBox(takeObject(arg0));
    return addHeapObject(ret);
};

module.exports.__wbg_showOpenDialog_19ea06987fab325f = function(arg0) {
    var ret = window2.showOpenDialog(takeObject(arg0));
    return addHeapObject(ret);
};

module.exports.__wbg_showQuickPick_1d8065c24240b264 = function(arg0, arg1) {
    var ret = window2.showQuickPick(getObject(arg0), takeObject(arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_showTextDocument_980643676b58f352 = function(arg0) {
    var ret = window2.showTextDocument(getObject(arg0));
    return addHeapObject(ret);
};

module.exports.__wbg_showWarningMessage_90b5ea489be3aed6 = function(arg0, arg1, arg2, arg3, arg4) {
    var v0 = getArrayJsValueFromWasm0(arg3, arg4).slice();
    wasm.__wbindgen_free(arg3, arg4 * 4);
    var ret = window2.showWarningMessage(getStringFromWasm0(arg0, arg1), getObject(arg2), ...v0);
    return addHeapObject(ret);
};

module.exports.__wbg_withProgress_97109f20cefc51a5 = function(arg0, arg1) {
    window2.withProgress(takeObject(arg0), takeObject(arg1));
};

module.exports.__wbg_static_accessor_ACTIVE_TEXT_EDITOR_13d9b61ca51bca0c = function() {
    var ret = window2.activeTextEditor;
    return isLikeNone(ret) ? 0 : addHeapObject(ret);
};

module.exports.__wbg_static_accessor_VISIBLE_TEXT_EDITORS_2a8dd4f394d5ee1c = function() {
    var ret = window2.visibleTextEditors;
    return addHeapObject(ret);
};

module.exports.__wbg_findFiles_e3c3cda43c3febf1 = function(arg0, arg1) {
    var ret = workspace.findFiles(getStringFromWasm0(arg0, arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_getConfiguration_5d6b258874954efd = function(arg0, arg1) {
    var ret = workspace.getConfiguration(getStringFromWasm0(arg0, arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_openTextDocument_920e3629f1673b4f = function(arg0, arg1) {
    var ret = workspace.openTextDocument(getStringFromWasm0(arg0, arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_saveAll_19b5ba111e14f406 = function(arg0) {
    var ret = workspace.saveAll(arg0 !== 0);
    return addHeapObject(ret);
};

module.exports.__wbg_static_accessor_ROOT_PATH_80351d06003c54e4 = function() {
    var ret = workspace.rootPath;
    return addHeapObject(ret);
};

module.exports.__wbindgen_is_function = function(arg0) {
    var ret = typeof(getObject(arg0)) === 'function';
    return ret;
};

module.exports.__wbg_value_c9ae6368b110a068 = function(arg0) {
    var ret = getObject(arg0).value;
    return addHeapObject(ret);
};

module.exports.__wbg_new_9dff83a08f5994f3 = function() {
    var ret = new Array();
    return addHeapObject(ret);
};

module.exports.__wbg_get_5fa3f454aa041e6e = function(arg0, arg1) {
    var ret = getObject(arg0)[arg1 >>> 0];
    return addHeapObject(ret);
};

module.exports.__wbg_isArray_cf56c8363b1b35d9 = function(arg0) {
    var ret = Array.isArray(getObject(arg0));
    return ret;
};

module.exports.__wbg_length_d2491466819b6271 = function(arg0) {
    var ret = getObject(arg0).length;
    return ret;
};

module.exports.__wbg_of_f769bf63504a0a14 = function(arg0) {
    var ret = Array.of(getObject(arg0));
    return addHeapObject(ret);
};

module.exports.__wbg_of_3a4bb382824dd437 = function(arg0, arg1) {
    var ret = Array.of(getObject(arg0), getObject(arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_push_3ddd8187ff2ff82d = function(arg0, arg1) {
    var ret = getObject(arg0).push(getObject(arg1));
    return ret;
};

module.exports.__wbg_values_f28e313e2260a03a = function(arg0) {
    var ret = getObject(arg0).values();
    return addHeapObject(ret);
};

module.exports.__wbg_instanceof_Error_659a8e367bd8a8e3 = function(arg0) {
    var ret = getObject(arg0) instanceof Error;
    return ret;
};

module.exports.__wbg_new_94a7dfa9529ec6e8 = function(arg0, arg1) {
    var ret = new Error(getStringFromWasm0(arg0, arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_message_36191aebccd723bd = function(arg0) {
    var ret = getObject(arg0).message;
    return addHeapObject(ret);
};

module.exports.__wbg_setmessage_5fcb11e7f60d9ab5 = function(arg0, arg1, arg2) {
    getObject(arg0).message = getStringFromWasm0(arg1, arg2);
};

module.exports.__wbg_setname_3b4b98a44f7164ab = function(arg0, arg1, arg2) {
    getObject(arg0).name = getStringFromWasm0(arg1, arg2);
};

module.exports.__wbg_newnoargs_7c6bd521992b4022 = function(arg0, arg1) {
    var ret = new Function(getStringFromWasm0(arg0, arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_call_951bd0c6d815d6f1 = handleError(function(arg0, arg1) {
    var ret = getObject(arg0).call(getObject(arg1));
    return addHeapObject(ret);
});

module.exports.__wbg_call_bf745b1758bb6693 = handleError(function(arg0, arg1, arg2) {
    var ret = getObject(arg0).call(getObject(arg1), getObject(arg2));
    return addHeapObject(ret);
});

module.exports.__wbg_next_373211328013f949 = handleError(function(arg0) {
    var ret = getObject(arg0).next();
    return addHeapObject(ret);
});

module.exports.__wbg_done_49c598117f977077 = function(arg0) {
    var ret = getObject(arg0).done;
    return ret;
};

module.exports.__wbg_getTimezoneOffset_b9f3c4664b1a35ae = function(arg0) {
    var ret = getObject(arg0).getTimezoneOffset();
    return ret;
};

module.exports.__wbg_new0_abd359df4aeb5b55 = function() {
    var ret = new Date();
    return addHeapObject(ret);
};

module.exports.__wbg_now_ba10664caf7c834a = function() {
    var ret = Date.now();
    return ret;
};

module.exports.__wbg_instanceof_Object_cdaa71ad2ca2f4c5 = function(arg0) {
    var ret = getObject(arg0) instanceof Object;
    return ret;
};

module.exports.__wbg_entries_7144a7309b22df64 = function(arg0) {
    var ret = Object.entries(getObject(arg0));
    return addHeapObject(ret);
};

module.exports.__wbg_new_ba07d0daa0e4677e = function() {
    var ret = new Object();
    return addHeapObject(ret);
};

module.exports.__wbg_apply_bcaf00c3d1ffaca7 = handleError(function(arg0, arg1, arg2) {
    var ret = Reflect.apply(getObject(arg0), getObject(arg1), getObject(arg2));
    return addHeapObject(ret);
});

module.exports.__wbg_get_85e0a3b459845fe2 = handleError(function(arg0, arg1) {
    var ret = Reflect.get(getObject(arg0), getObject(arg1));
    return addHeapObject(ret);
});

module.exports.__wbg_ownKeys_d44c25f33e28bfab = handleError(function(arg0) {
    var ret = Reflect.ownKeys(getObject(arg0));
    return addHeapObject(ret);
});

module.exports.__wbg_set_9bdd413385146137 = handleError(function(arg0, arg1, arg2) {
    var ret = Reflect.set(getObject(arg0), getObject(arg1), getObject(arg2));
    return ret;
});

module.exports.__wbg_buffer_3f12a1c608c6d04e = function(arg0) {
    var ret = getObject(arg0).buffer;
    return addHeapObject(ret);
};

module.exports.__wbg_new_bb4e44ef089e45b4 = function(arg0, arg1) {
    try {
        var state0 = {a: arg0, b: arg1};
        var cb0 = (arg0, arg1) => {
            const a = state0.a;
            state0.a = 0;
            try {
                return __wbg_adapter_347(a, state0.b, arg0, arg1);
            } finally {
                state0.a = a;
            }
        };
        var ret = new Promise(cb0);
        return addHeapObject(ret);
    } finally {
        state0.a = state0.b = 0;
    }
};

module.exports.__wbg_resolve_6e61e640925a0db9 = function(arg0) {
    var ret = Promise.resolve(getObject(arg0));
    return addHeapObject(ret);
};

module.exports.__wbg_then_dd3785597974798a = function(arg0, arg1) {
    var ret = getObject(arg0).then(getObject(arg1));
    return addHeapObject(ret);
};

module.exports.__wbg_then_0f957e0f4c3e537a = function(arg0, arg1, arg2) {
    var ret = getObject(arg0).then(getObject(arg1), getObject(arg2));
    return addHeapObject(ret);
};

module.exports.__wbg_self_6baf3a3aa7b63415 = handleError(function() {
    var ret = self.self;
    return addHeapObject(ret);
});

module.exports.__wbg_window_63fc4027b66c265b = handleError(function() {
    var ret = window.window;
    return addHeapObject(ret);
});

module.exports.__wbg_globalThis_513fb247e8e4e6d2 = handleError(function() {
    var ret = globalThis.globalThis;
    return addHeapObject(ret);
});

module.exports.__wbg_global_b87245cd886d7113 = handleError(function() {
    var ret = global.global;
    return addHeapObject(ret);
});

module.exports.__wbg_newwithbyteoffsetandlength_4c51342f87299c5a = function(arg0, arg1, arg2) {
    var ret = new Uint8Array(getObject(arg0), arg1 >>> 0, arg2 >>> 0);
    return addHeapObject(ret);
};

module.exports.__wbg_new_c6c0228e6d22a2f9 = function(arg0) {
    var ret = new Uint8Array(getObject(arg0));
    return addHeapObject(ret);
};

module.exports.__wbg_length_c645e7c02233b440 = function(arg0) {
    var ret = getObject(arg0).length;
    return ret;
};

module.exports.__wbg_set_b91afac9fd216d99 = function(arg0, arg1, arg2) {
    getObject(arg0).set(getObject(arg1), arg2 >>> 0);
};

module.exports.__wbindgen_number_get = function(arg0, arg1) {
    const obj = getObject(arg1);
    var ret = typeof(obj) === 'number' ? obj : undefined;
    getFloat64Memory0()[arg0 / 8 + 1] = isLikeNone(ret) ? 0 : ret;
    getInt32Memory0()[arg0 / 4 + 0] = !isLikeNone(ret);
};

module.exports.__wbindgen_is_string = function(arg0) {
    var ret = typeof(getObject(arg0)) === 'string';
    return ret;
};

module.exports.__wbindgen_string_get = function(arg0, arg1) {
    const obj = getObject(arg1);
    var ret = typeof(obj) === 'string' ? obj : undefined;
    var ptr0 = isLikeNone(ret) ? 0 : passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbindgen_boolean_get = function(arg0) {
    const v = getObject(arg0);
    var ret = typeof(v) === 'boolean' ? (v ? 1 : 0) : 2;
    return ret;
};

module.exports.__wbindgen_debug_string = function(arg0, arg1) {
    var ret = debugString(getObject(arg1));
    var ptr0 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
    var len0 = WASM_VECTOR_LEN;
    getInt32Memory0()[arg0 / 4 + 1] = len0;
    getInt32Memory0()[arg0 / 4 + 0] = ptr0;
};

module.exports.__wbindgen_throw = function(arg0, arg1) {
    throw new Error(getStringFromWasm0(arg0, arg1));
};

module.exports.__wbindgen_memory = function() {
    var ret = wasm.memory;
    return addHeapObject(ret);
};

module.exports.__wbindgen_closure_wrapper807 = function(arg0, arg1, arg2) {
    var ret = makeMutClosure(arg0, arg1, 12, __wbg_adapter_34);
    return addHeapObject(ret);
};

module.exports.__wbindgen_closure_wrapper809 = function(arg0, arg1, arg2) {
    var ret = makeMutClosure(arg0, arg1, 8, __wbg_adapter_37);
    return addHeapObject(ret);
};

module.exports.__wbindgen_closure_wrapper811 = function(arg0, arg1, arg2) {
    var ret = makeMutClosure(arg0, arg1, 10, __wbg_adapter_40);
    return addHeapObject(ret);
};

module.exports.__wbindgen_closure_wrapper11632 = function(arg0, arg1, arg2) {
    var ret = makeMutClosure(arg0, arg1, 1964, __wbg_adapter_43);
    return addHeapObject(ret);
};

module.exports.__wbindgen_closure_wrapper11634 = function(arg0, arg1, arg2) {
    var ret = makeMutClosure(arg0, arg1, 1962, __wbg_adapter_46);
    return addHeapObject(ret);
};

module.exports.__wbindgen_closure_wrapper12689 = function(arg0, arg1, arg2) {
    var ret = makeMutClosure(arg0, arg1, 2074, __wbg_adapter_49);
    return addHeapObject(ret);
};

const path = require('path').join(__dirname, 'icie_bg.wasm');
const bytes = require('fs').readFileSync(path);

const wasmModule = new WebAssembly.Module(bytes);
const wasmInstance = new WebAssembly.Instance(wasmModule, imports);
wasm = wasmInstance.exports;
module.exports.__wasm = wasm;

