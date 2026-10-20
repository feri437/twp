/**
 * TWP-CF Telegram Web Proxy — single-file Worker
 * Bundled from TWP-CF modules (2026.10.08)
 *
 * Required:
 *   PROXY_SECRET (secret) — 32 hex chars, optional dd prefix
 *   SESSIONS (Durable Object) — class WebProxySession (SQLite)
 *
 * Optional:
 *   PUBLIC_HOSTNAME — e.g. name.subdomain.workers.dev
 *
 * Telegram link:
 *   https://t.me/webproxy?server=HOST&secret=SECRET
 */

import { connect } from "cloudflare:sockets";

/* ===== protocol.js ===== */
const FRAME = Object.freeze({
  OPEN: 0x01,
  DATA: 0x02,
  CLOSE: 0x03,
  WINDOW: 0x04,
  PING: 0x05,
  PONG: 0x06,
  HELLO: 0x10,
  WELCOME: 0x11,
  BYE: 0x1f,
});

const HEADER_SIZE = 8;
const MAX_PAYLOAD = 1024 * 1024;
const MAX_BATCH_FRAMES = 4096;
const INITIAL_WINDOW = 4 * 1024 * 1024;
const DATA_CHUNK = 64 * 1024;
const MAX_WS_MESSAGE = 2 * 1024 * 1024;

function encodeFrame(type, streamId, payload = new Uint8Array()) {
  if (streamId < 0 || streamId > 0xffffff || payload.length > MAX_PAYLOAD) throw new Error("invalid frame");
  const out = new Uint8Array(HEADER_SIZE + payload.length);
  out[0] = type; out[1] = streamId >>> 16; out[2] = streamId >>> 8; out[3] = streamId;
  new DataView(out.buffer).setUint32(4, payload.length);
  out.set(payload, HEADER_SIZE);
  return out;
}

function parseFrames(input) {
  const frames = []; let offset = 0;
  while (offset < input.length) {
    if (frames.length >= MAX_BATCH_FRAMES || input.length - offset < HEADER_SIZE) throw new Error("bad batch");
    const view = new DataView(input.buffer, input.byteOffset + offset, HEADER_SIZE);
    const length = view.getUint32(4);
    if (length > MAX_PAYLOAD || offset + HEADER_SIZE + length > input.length) throw new Error("bad payload");
    frames.push({ type: input[offset], streamId: (input[offset + 1] << 16) | (input[offset + 2] << 8) | input[offset + 3], payload: input.subarray(offset + HEADER_SIZE, offset + HEADER_SIZE + length) });
    offset += HEADER_SIZE + length;
  }
  if (!frames.length) throw new Error("empty batch");
  return frames;
}


function u32(value) { const out = new Uint8Array(4); new DataView(out.buffer).setUint32(0, value); return out; }
function clampInt(value, min, max, fallback) { const n = Number.parseInt(value, 10); return Number.isFinite(n) ? Math.min(max, Math.max(min, n)) : fallback; }

/* ===== mtproxy.js ===== */
const TAGS = new Set([0xefefefef, 0xeeeeeeee, 0xdddddddd]);
const TELEGRAM_DCS = Object.freeze({1:"149.154.175.50",2:"149.154.167.51",3:"149.154.175.100",4:"149.154.167.91",5:"149.154.171.5"});

class AesCtrStream {
  constructor(keyBytes, ivBytes) {
    if (keyBytes.length !== 32 || ivBytes.length !== 16) throw new Error("bad AES material");
    this.keyPromise = crypto.subtle.importKey("raw", keyBytes, "AES-CTR", false, ["encrypt"]);
    this.counter = new Uint8Array(ivBytes);
    this.spare = new Uint8Array();
  }
  async crypt(input) {
    const src = input instanceof Uint8Array ? input : new Uint8Array(input);
    const out = new Uint8Array(src.length); let pos = 0;
    if (this.spare.length) {
      const n = Math.min(this.spare.length, src.length);
      for (let i=0;i<n;i++) out[i] = src[i] ^ this.spare[i];
      this.spare = this.spare.subarray(n); pos = n;
    }
    if (pos < src.length) {
      const need = src.length - pos, blocks = Math.ceil(need / 16);
      const zeros = new Uint8Array(blocks * 16);
      const key = await this.keyPromise;
      const ks = new Uint8Array(await crypto.subtle.encrypt({name:"AES-CTR",counter:this.counter,length:128}, key, zeros));
      addBlocks(this.counter, blocks);
      for (let i=0;i<need;i++) out[pos+i] = src[pos+i] ^ ks[i];
      if (need < ks.length) this.spare = ks.subarray(need);
    }
    return out;
  }
}

function addBlocks(counter, blocks) {
  let carry = blocks;
  for (let i=15;i>=0 && carry;i--) {
    const sum = counter[i] + (carry & 255);
    counter[i] = sum & 255;
    carry = Math.floor(carry / 256) + (sum >>> 8);
  }
}
function reverse(bytes){ return Uint8Array.from(bytes).reverse(); }
function concat(a,b){ const out=new Uint8Array(a.length+b.length); out.set(a); out.set(b,a.length); return out; }
async function sha256(bytes){ return new Uint8Array(await crypto.subtle.digest("SHA-256",bytes)); }
function parseProxySecret(value) {
  const s=String(value||"").toLowerCase();
  if (/^[0-9a-f]{32}$/.test(s)) return {bridge:hex(s), inner:hex(s), mode:"plain"};
  if (/^dd[0-9a-f]{32}$/.test(s)) return {bridge:hex(s), inner:hex(s.slice(2)), mode:"dd"};
  if (/^ee/.test(s)) throw new Error("FakeTLS secrets are not supported in WEB mode");
  throw new Error("PROXY_SECRET must be 32 hex characters, optionally prefixed with dd");
}
function hex(s){ const x=new Uint8Array(s.length/2); for(let i=0;i<x.length;i++)x[i]=parseInt(s.slice(i*2,i*2+2),16); return x; }

async function acceptClientHandshake(packet, secret) {
  if (packet.length !== 64) throw new Error("bad handshake length");
  const material = packet.subarray(8,56), rev=reverse(material);
  const decKey=await sha256(concat(material.subarray(0,32),secret));
  const dec=new AesCtrStream(decKey,material.subarray(32,48));
  const encKey=await sha256(concat(rev.subarray(0,32),secret));
  const enc=new AesCtrStream(encKey,rev.subarray(32,48));
  const plain=await dec.crypt(packet);
  const view=new DataView(plain.buffer,plain.byteOffset,plain.byteLength);
  const tag=view.getUint32(56,true), dcId=view.getInt16(60,true);
  if(!TAGS.has(tag) || !TELEGRAM_DCS[Math.abs(dcId)]) throw new Error("invalid MTProxy handshake");
  return {tag,dcId,clientDecrypt:dec,clientEncrypt:enc};
}

async function createTelegramHandshake(tag, dcId) {
  let nonce;
  do { nonce=new Uint8Array(64); crypto.getRandomValues(nonce); } while (reserved(nonce));
  const v=new DataView(nonce.buffer); v.setUint32(56,tag,true); v.setInt16(60,dcId,true); nonce[62]=nonce[63]=0;
  const material=nonce.subarray(8,56), rev=reverse(material);
  const encrypt=new AesCtrStream(material.subarray(0,32),material.subarray(32,48));
  const decrypt=new AesCtrStream(rev.subarray(0,32),rev.subarray(32,48));
  const encrypted=await encrypt.crypt(nonce);
  const wire=new Uint8Array(nonce); wire.set(encrypted.subarray(56),56);
  return {wire,encrypt,decrypt};
}
function reserved(n){
  const v=new DataView(n.buffer,n.byteOffset,n.byteLength), x=v.getUint32(0,true);
  return n[0]===0xef || x===0x44414548 || x===0x54534f50 || x===0x20544547 || x===0xeeeeeeee || x===0xdddddddd || v.getUint32(4,true)===0;
}

/* ===== bridge.js ===== */

function bridgePage(host, bootstrap) {
  const scriptNonce = randomNonce();
  const config = JSON.stringify({ origin: `https://${host}`, bootstrap, batchLimit: MAX_WS_MESSAGE, maxPendingItems: 1024, connectTimeout: 15000 });
  const html = `<!doctype html>
<html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Web Proxy</title></head>
<body><main><h1>Connection bridge</h1><p>This page is opened by a compatible Telegram client.</p></main>
<script nonce="${scriptNonce}">
(()=>{'use strict';
const cfg=${config};
let port=null, sessionToken='', socket=null, creating=false, closed=false;
const pending=[]; let pendingBytes=0;
const bootstrapAbort=new AbortController(); let connectTimer=null;
const fragment=new URLSearchParams(location.hash.slice(1));
const nonce=fragment.get('android')||'';
history.replaceState(null,'','/');
function status(state){try{port&&port.postMessage({t:'status',state})}catch{}}
function splitFrames(buffer){
 const input=new Uint8Array(buffer); let off=0,count=0,out=[];
 while(off<input.length){
  if(++count>4096||input.length-off<8)throw Error('bad frame');
  const view=new DataView(input.buffer,input.byteOffset+off,8); const len=view.getUint32(4);
  if(len>1048576||off+8+len>input.length)throw Error('bad frame');
  out.push(buffer.slice(off,off+8+len)); off+=8+len;
 }
 if(!out.length)throw Error('empty'); return out;
}
function sendToApp(buffer){for(const frame of splitFrames(buffer))port.postMessage(frame,[frame]);}
function fail(){if(closed)return;status('failed');close(false)}
async function createSession(hello){
 try{
  const response=await fetch(cfg.origin+'/api/v1/session',{method:'POST',headers:{Authorization:'Bearer '+cfg.bootstrap,'Content-Type':'application/octet-stream','X-Carrier-Mode':'websocket'},body:hello,mode:'same-origin',redirect:'error',cache:'no-store',credentials:'omit',referrerPolicy:'no-referrer',signal:bootstrapAbort.signal});
  if(!response.ok||response.headers.get('X-Carrier-Mode')!=='websocket')throw Error('session');
  sessionToken=response.headers.get('X-Session-Token')||'';
  if(!/^[A-Za-z0-9_-]{43}$/.test(sessionToken))throw Error('token');
  const welcome=await response.arrayBuffer();
  if(closed)return;
  if(welcome.byteLength!==8||new Uint8Array(welcome)[0]!==0x11||new Uint8Array(welcome).slice(1).some(v=>v!==0))throw Error('welcome');
  sendToApp(welcome);
  if(!closed)openSocket();
 }catch(e){fail()}
}
function openSocket(){
 const target=cfg.origin.replace(/^https:/,'wss:')+'/api/v1/ws';
 socket=new WebSocket(target,'tproxy-v1.'+sessionToken); socket.binaryType='arraybuffer';
 socket.onopen=()=>{
  if(closed)return; clearTimeout(connectTimer);connectTimer=null;status('connected');
  try{for(const data of pending){if(socket.bufferedAmount+data.byteLength>cfg.batchLimit)return fail();socket.send(data)}}catch{return fail()}
  pending.length=0;pendingBytes=0;
 };
 socket.onmessage=e=>{if(closed)return;if(!(e.data instanceof ArrayBuffer)||!e.data.byteLength||e.data.byteLength>cfg.batchLimit)return fail();try{sendToApp(e.data)}catch{return fail()}};
 socket.onerror=()=>{}; socket.onclose=()=>{if(!closed)fail()};
}
function fromApp(data){
 if(closed)return;
 if(data instanceof ArrayBuffer){
  if(!data.byteLength||data.byteLength>cfg.batchLimit)return fail();
  try{splitFrames(data)}catch{return fail()}
  if(!creating){creating=true;connectTimer=setTimeout(fail,cfg.connectTimeout);createSession(data);return}
  if(!sessionToken||!socket||socket.readyState!==WebSocket.OPEN){if(pending.length>=cfg.maxPendingItems||pendingBytes+data.byteLength>cfg.batchLimit)return fail();pending.push(data);pendingBytes+=data.byteLength;return}
  if(socket.bufferedAmount+data.byteLength>cfg.batchLimit)return fail();
  try{socket.send(data)}catch{fail()}
 }else if(data&&data.t==='close')close(true);
}
function activate(next){port=next;port.onmessage=e=>fromApp(e.data);port.start&&port.start();status('connecting')}
const native=globalThis.TelegramWebProxy;
if(/^[A-Za-z0-9_-]{43}$/.test(nonce)&&native&&typeof native.postMessage==='function'){
 const adapter={onmessage:null,start(){},close(){native.onmessage=null},postMessage(value){
  if(value instanceof ArrayBuffer){for(const frame of splitFrames(value))native.postMessage(frame)}
  else native.postMessage(JSON.stringify(value));
 }};
 native.onmessage=e=>{let d=e.data;if(typeof d==='string'){try{d=JSON.parse(d)}catch{return}}adapter.onmessage&&adapter.onmessage({data:d})};
 activate(adapter);native.postMessage(JSON.stringify({t:'tproxy-android-init',v:1,nonce}));
}
addEventListener('message',e=>{
 if(closed||port||e.source!==parent||!e.data||e.data.t!=='tproxy-init'||e.data.v!==1||e.ports.length!==1)return;
 try{const u=new URL(e.origin);if(u.protocol!=='http:'||u.hostname!=='127.0.0.1'||!u.port)return}catch{return}
 activate(e.ports[0]);
});
function close(notify){if(closed)return;closed=true;clearTimeout(connectTimer);connectTimer=null;bootstrapAbort.abort();pending.length=0;pendingBytes=0;try{socket&&socket.close()}catch{}if(notify&&sessionToken)fetch(cfg.origin+'/api/v1/session',{method:'DELETE',headers:{Authorization:'Bearer '+sessionToken},keepalive:true,mode:'same-origin',redirect:'error',cache:'no-store',credentials:'omit',referrerPolicy:'no-referrer'}).catch(()=>{});try{port&&port.close()}catch{}}
addEventListener('pagehide',()=>close(true),{once:true});
})();
</script></body></html>`;
  return new Response(html, {
    headers: {
      "Content-Type": "text/html; charset=utf-8",
      "Cache-Control": "no-store",
      "Content-Security-Policy": `default-src 'none'; script-src 'nonce-${scriptNonce}'; connect-src https://${host} wss://${host}; style-src 'none'; img-src 'none'; object-src 'none'; worker-src 'none'; base-uri 'none'; form-action 'none'; frame-ancestors http://127.0.0.1:*; sandbox allow-same-origin allow-scripts`,
      "Referrer-Policy": "no-referrer",
      "X-Content-Type-Options": "nosniff",
      "Permissions-Policy": "camera=(), microphone=(), geolocation=()",
    },
  });
}

function randomNonce() { const bytes = crypto.getRandomValues(new Uint8Array(18)); return btoa(String.fromCharCode(...bytes)); }

/* ===== session.js ===== */

// Bounds include frame headers and an allowance for each retained queue item.
const LIMITS = Object.freeze({
  itemCost: 256,
  ingressBytes: 8 * 1024 * 1024,
  ingressItems: 128,
  uplinkBytes: 8 * 1024 * 1024,
  uplinkItems: 8192,
  streamBytes: INITIAL_WINDOW + 1024 * 1024,
  streamItems: 4096,
  downlinkBytes: 8 * 1024 * 1024,
  downlinkItems: 8192,
  handshakeTimeout: 15000,
  connectTimeout: 10000,
  writeTimeout: 30000,
});

// The Workers entrypoint supplies cloudflare:sockets.connect. Keeping the
// transport injectable lets tests exercise real framing/crypto with fake I/O.
class RelaySession {
  constructor(ctx, env, connect) {
    this.ctx = ctx;
    this.env = env;
    this.connect = connect;
    this.initialized = false;
    this.closed = false;
    this.ws = null;
    this.streams = new Map();
    this.closedIds = new Set();
    this.maxStreams = clampInt(env.MAX_STREAMS, 1, 128, 64);
    this.diagnostics = String(env.DIAGNOSTICS || "") === "1";
    this.traceId = this.diagnostics ? crypto.randomUUID().slice(0, 8) : null;
    this.messageCount = 0;
    this.messageChain = Promise.resolve();
    this.ingressBytes = 0;
    this.ingressItems = 0;
    this.uplinkBytes = 0;
    this.uplinkItems = 0;
    this.downlinkBytes = 0;
    this.downlinkItems = 0;
    this.downlinkWaiters = new Set();
    this.secret = null;
  }

  trace(event, details = {}) {
    if (this.diagnostics) console.log("webproxy", { traceId: this.traceId, event, ...details });
  }

  async fetch(request) {
    const url = new URL(request.url);
    if (this.closed) return new Response("session closed", { status: 404 });
    if (url.pathname === "/internal/init" && request.method === "POST") {
      if (!this.initialized) {
        await this.ctx.storage.put({ expiresAt: Date.now() + 10 * 60 * 1000 });
        this.initialized = true;
      }
      return new Response(null, { status: 204 });
    }
    if (url.pathname === "/internal/ws" && request.headers.get("Upgrade")?.toLowerCase() === "websocket") {
      if (!this.initialized) {
        const expiresAt = await this.ctx.storage.get("expiresAt");
        if (this.closed || !expiresAt || expiresAt < Date.now()) return new Response("unknown session", { status: 404 });
        this.initialized = true;
      }
      if (this.ws) return new Response("already connected", { status: 409 });
      const pair = new WebSocketPair();
      const client = pair[0], server = pair[1];
      server.accept();
      this.ws = server;
      this.trace("websocket_accepted");
      server.addEventListener("message", (event) => this.enqueueMessage(event.data));
      server.addEventListener("close", (event) => {
        this.trace("websocket_closed", { code: event.code, clean: event.wasClean });
        this.shutdown("websocket_close");
      });
      server.addEventListener("error", () => this.shutdown("websocket_error"));
      const protocol = request.headers.get("X-TProxy-Protocol") || "";
      return new Response(null, { status: 101, webSocket: client,
        headers: protocol ? { "Sec-WebSocket-Protocol": protocol } : {} });
    }
    if (url.pathname === "/internal/close" && request.method === "POST") {
      this.shutdown("session_delete");
      return new Response(null, { status: 204 });
    }
    return new Response("not found", { status: 404 });
  }

  enqueueMessage(data) {
    if (this.closed) return;
    const length = data instanceof Blob ? data.size : data instanceof ArrayBuffer ? data.byteLength : 0;
    if (!length || length > MAX_WS_MESSAGE) return this.protocolError("invalid_websocket_message");
    const cost = length + LIMITS.itemCost;
    if (this.ingressBytes + cost > LIMITS.ingressBytes || this.ingressItems >= LIMITS.ingressItems) {
      return this.protocolError("ingress_queue_limit");
    }
    this.ingressBytes += cost;
    this.ingressItems++;
    // Only decode/dispatch is serialized (including async Blob conversion).
    // TCP dialing, writes and crypto run independently in each stream's FIFO.
    this.messageChain = this.messageChain.then(() => this.onMessage(data))
      .catch(() => this.protocolError("message_handler_failed"))
      .finally(() => { this.ingressBytes -= cost; this.ingressItems--; });
    this.ctx.waitUntil(this.messageChain);
    return this.messageChain;
  }

  async onMessage(data) {
    if (this.closed) return;
    if (data instanceof Blob) data = await data.arrayBuffer();
    if (this.closed) return;
    if (!(data instanceof ArrayBuffer) || !data.byteLength || data.byteLength > MAX_WS_MESSAGE) {
      return this.protocolError("invalid_websocket_message");
    }
    let frames;
    try { frames = parseFrames(new Uint8Array(data)); }
    catch { return this.protocolError("frame_parse_failed"); }
    if (this.diagnostics) {
      this.trace("frames_received", { message: ++this.messageCount, bytes: data.byteLength,
        frames: frames.map(({ type, streamId, payload }) => ({ type, streamId, length: payload.length })) });
    }
    for (const frame of frames) {
      if (frame.streamId === 0) {
        if (frame.type !== FRAME.PONG || frame.payload.length > 64) return this.protocolError("invalid_control_frame");
      } else if (frame.type === FRAME.OPEN) this.openStream(frame);
      else if (frame.type === FRAME.DATA) this.queueWrite(frame);
      else if (frame.type === FRAME.WINDOW) this.addWindow(frame);
      else if (frame.type === FRAME.CLOSE) {
        if (frame.payload.length) return this.protocolError("invalid_close");
        if (!this.streams.has(frame.streamId) && !this.closedIds.has(frame.streamId)) return this.protocolError("unknown_stream");
        this.closeStream(frame.streamId, false);
      } else return this.protocolError("unknown_frame_type");
      if (this.closed) return;
    }
  }

  openStream(frame) {
    const id = frame.streamId;
    if (!id || frame.payload.length || this.streams.has(id) || this.closedIds.has(id)) return this.protocolError("invalid_open");
    if (this.streams.size >= this.maxStreams) { this.rememberClosed(id); return this.sendFrame(FRAME.CLOSE, id); }
    const stream = { id, socket: null, writer: null, handshake: new Uint8Array(), handshakeBytes: 0,
      receiveWindow: INITIAL_WINDOW, sendCredit: INITIAL_WINDOW, closed: false,
      queue: [], queueHead: 0, pendingBytes: 0, pendingItems: 0, draining: false,
      abort: new AbortController(), sent: [], sentHead: 0, downlinkBytes: 0, downlinkItems: 0 };
    stream.handshakeTimer = setTimeout(() => {
      this.trace("handshake_timeout", { streamId: id });
      this.closeStream(id, true);
    }, LIMITS.handshakeTimeout);
    this.streams.set(id, stream);
    this.trace("stream_opened", { streamId: id });
  }

  queueWrite(frame) {
    const stream = this.streams.get(frame.streamId);
    if (!stream) {
      if (this.closedIds.has(frame.streamId) && frame.payload.length) return;
      return this.protocolError("unknown_stream");
    }
    const length = frame.payload.length;
    if (!length || length > stream.receiveWindow) return this.protocolError("invalid_data_window");
    const cost = length + HEADER_SIZE + LIMITS.itemCost;
    if (stream.pendingBytes + cost > LIMITS.streamBytes || stream.pendingItems >= LIMITS.streamItems ||
        this.uplinkBytes + cost > LIMITS.uplinkBytes || this.uplinkItems >= LIMITS.uplinkItems) {
      this.trace("uplink_queue_limit", { streamId: stream.id });
      return this.closeStream(stream.id, true);
    }
    stream.receiveWindow -= length; // Admission, not completion, consumes credit.
    stream.pendingBytes += cost; stream.pendingItems++;
    this.uplinkBytes += cost; this.uplinkItems++;
    // Copy so one tiny queued frame cannot retain a whole 2 MiB carrier batch.
    stream.queue.push({ payload: new Uint8Array(frame.payload), cost });
    if (!stream.draining) {
      stream.draining = true;
      this.ctx.waitUntil(this.drainStream(stream));
    }
  }

  releaseWrite(stream, item) {
    stream.pendingBytes -= item.cost; stream.pendingItems--;
    this.uplinkBytes -= item.cost; this.uplinkItems--;
  }

  async drainStream(stream) {
    try {
      while (!stream.closed && !this.closed && stream.queueHead < stream.queue.length) {
        const item = stream.queue[stream.queueHead];
        stream.queue[stream.queueHead++] = null;
        try { await this.writeStream(stream, item.payload); }
        finally { this.releaseWrite(stream, item); }
        if (stream.queueHead === stream.queue.length) { stream.queue = []; stream.queueHead = 0; }
        else if (stream.queueHead >= 64) { stream.queue = stream.queue.slice(stream.queueHead); stream.queueHead = 0; }
      }
    } catch (error) {
      this.trace("stream_write_failed", { streamId: stream.id, stage: stream.writer ? "relay" : "handshake_or_connect", error: safeError(error) });
      this.closeStream(stream.id, true);
    } finally { stream.draining = false; }
  }

  active(stream) {
    if (stream.closed || this.closed) throw new Error("stream closed");
  }

  async writeStream(stream, payload) {
    this.active(stream);
    let grant = payload.length;
    if (!stream.writer) {
      // Only retain the 64-byte handshake, not all pre-authentication DATA.
      const take = Math.min(64 - stream.handshake.length, payload.length);
      const joined = new Uint8Array(stream.handshake.length + take);
      joined.set(stream.handshake); joined.set(payload.subarray(0, take), stream.handshake.length);
      stream.handshake = joined;
      stream.handshakeBytes += take;
      if (joined.length < 64) return; // Do not acknowledge unvalidated partial handshakes.
      if (!this.secret) this.secret = parseProxySecret(this.env.PROXY_SECRET).inner;
      const client = await acceptClientHandshake(joined, this.secret);
      this.active(stream);
      const tg = await createTelegramHandshake(client.tag, client.dcId);
      this.active(stream);
      clearTimeout(stream.handshakeTimer); stream.handshakeTimer = null;
      const started = this.diagnostics ? Date.now() : 0;
      const socket = this.connect({ hostname: TELEGRAM_DCS[Math.abs(client.dcId)], port: 443 }, { allowHalfOpen: false });
      stream.socket = socket; // Track before awaiting: CLOSE must cancel in-flight dials.
      Promise.resolve(socket.closed).catch(() => {});
      await waitFor(socket.opened, stream.abort.signal, LIMITS.connectTimeout, "connect timeout");
      this.active(stream);
      this.trace("telegram_dc_connected", { streamId: stream.id, dcId: client.dcId, connectMs: started ? Date.now() - started : undefined });
      stream.writer = socket.writable.getWriter();
      stream.clientDecrypt = client.clientDecrypt; stream.clientEncrypt = client.clientEncrypt;
      stream.tgEncrypt = tg.encrypt; stream.tgDecrypt = tg.decrypt;
      stream.handshake = new Uint8Array();
      await waitFor(stream.writer.write(tg.wire), stream.abort.signal, LIMITS.writeTimeout, "write timeout");
      this.active(stream);
      this.ctx.waitUntil(this.readStream(stream));
      grant = stream.handshakeBytes + payload.length - take;
      stream.handshakeBytes = 0;
      payload = payload.subarray(take);
    }
    // Bound temporary crypto buffers; FIFO preserves the CTR position.
    for (let offset = 0; offset < payload.length; offset += DATA_CHUNK) {
      const plain = await stream.clientDecrypt.crypt(payload.subarray(offset, offset + DATA_CHUNK));
      this.active(stream);
      const encrypted = await stream.tgEncrypt.crypt(plain);
      this.active(stream);
      await waitFor(stream.writer.write(encrypted), stream.abort.signal, LIMITS.writeTimeout, "write timeout");
      this.active(stream);
    }
    this.grantWindow(stream, grant);
  }

  grantWindow(stream, length) {
    if (stream.closed || this.closed || !length) return;
    stream.receiveWindow += length;
    this.sendFrame(FRAME.WINDOW, stream.id, u32(length));
  }

  addWindow(frame) {
    if (frame.payload.length !== 4) return this.protocolError("invalid_window");
    const amount = new DataView(frame.payload.buffer, frame.payload.byteOffset, 4).getUint32(0);
    if (!amount) return this.protocolError("invalid_window");
    const stream = this.streams.get(frame.streamId);
    if (!stream) {
      if (this.closedIds.has(frame.streamId)) return;
      return this.protocolError("unknown_stream");
    }
    // Credit represents bytes drained by the client, not a way to grow memory.
    if (amount > INITIAL_WINDOW - stream.sendCredit) return this.protocolError("window_overflow");
    stream.sendCredit += amount;
    let remaining = amount;
    while (remaining) {
      const item = stream.sent[stream.sentHead];
      const used = Math.min(remaining, item.remaining);
      item.remaining -= used; remaining -= used;
      stream.downlinkBytes -= used; this.downlinkBytes -= used;
      if (!item.remaining) {
        const overhead = HEADER_SIZE + LIMITS.itemCost;
        stream.downlinkBytes -= overhead; this.downlinkBytes -= overhead;
        stream.downlinkItems--; this.downlinkItems--;
        stream.sent[stream.sentHead++] = null;
      }
    }
    if (stream.sentHead === stream.sent.length) { stream.sent = []; stream.sentHead = 0; }
    else if (stream.sentHead >= 64) { stream.sent = stream.sent.slice(stream.sentHead); stream.sentHead = 0; }
    this.wakeDownlink();
  }

  downlinkRoom(stream) {
    if (this.downlinkItems >= LIMITS.downlinkItems) return 0;
    return Math.max(0, Math.min(DATA_CHUNK, stream.sendCredit,
      LIMITS.downlinkBytes - this.downlinkBytes - HEADER_SIZE - LIMITS.itemCost));
  }

  async waitDownlink(stream) {
    while (!stream.closed && !this.closed && !this.downlinkRoom(stream)) {
      await new Promise((resolve) => this.downlinkWaiters.add(resolve));
    }
    return !stream.closed && !this.closed;
  }

  wakeDownlink() {
    const waiters = [...this.downlinkWaiters];
    this.downlinkWaiters.clear();
    for (const resolve of waiters) resolve();
  }

  async readStream(stream) {
    const reader = stream.socket.readable.getReader();
    try {
      while (await this.waitDownlink(stream)) {
        const { value, done } = await reader.read();
        if (done || stream.closed || this.closed) break;
        const bytes = value instanceof Uint8Array ? value : new Uint8Array(value);
        let offset = 0;
        while (offset < bytes.length && await this.waitDownlink(stream)) {
          // Recheck after await: another stream may have consumed shared capacity.
          const size = Math.min(bytes.length - offset, this.downlinkRoom(stream));
          if (!size) continue;
          const cost = size + HEADER_SIZE + LIMITS.itemCost;
          stream.sendCredit -= size;
          stream.sent.push({ remaining: size });
          stream.downlinkBytes += cost; stream.downlinkItems++;
          this.downlinkBytes += cost; this.downlinkItems++;
          const plain = await stream.tgDecrypt.crypt(bytes.subarray(offset, offset + size));
          this.active(stream);
          const encrypted = await stream.clientEncrypt.crypt(plain);
          this.active(stream);
          this.sendFrame(FRAME.DATA, stream.id, encrypted);
          offset += size;
        }
      }
    } catch (error) { this.trace("stream_read_failed", { streamId: stream.id, error: safeError(error) }); }
    finally {
      ignoreFailure(() => reader.cancel());
      try { reader.releaseLock(); } catch {}
      this.closeStream(stream.id, true);
    }
  }

  closeStream(id, notify) {
    const stream = this.streams.get(id);
    if (!stream) return;
    this.streams.delete(id); this.rememberClosed(id);
    stream.closed = true;
    clearTimeout(stream.handshakeTimer); stream.handshakeTimer = null;
    stream.abort.abort();
    for (let i = stream.queueHead; i < stream.queue.length; i++) this.releaseWrite(stream, stream.queue[i]);
    stream.queue = []; stream.queueHead = 0; stream.handshake = new Uint8Array();
    this.downlinkBytes -= stream.downlinkBytes; this.downlinkItems -= stream.downlinkItems;
    stream.downlinkBytes = 0; stream.downlinkItems = 0; stream.sent = []; stream.sentHead = 0;
    this.wakeDownlink();
    ignoreFailure(() => stream.writer?.abort());
    ignoreFailure(() => stream.socket?.close());
    this.trace("stream_closed", { streamId: id, notify });
    if (notify && !this.closed) this.sendFrame(FRAME.CLOSE, id);
  }

  rememberClosed(id) {
    this.closedIds.add(id);
    if (this.closedIds.size > 4096) this.closedIds.delete(this.closedIds.values().next().value);
  }

  sendFrame(type, streamId, payload = new Uint8Array()) {
    if (this.closed || !this.ws || this.ws.readyState !== 1) return;
    try { this.ws.send(encodeFrame(type, streamId, payload)); }
    catch { this.shutdown("websocket_send_failed"); }
  }

  protocolError(reason = "protocol_error") {
    this.trace("protocol_error", { reason });
    this.sendFrame(FRAME.BYE, 0);
    this.shutdown(reason);
  }

  shutdown(reason = "shutdown") {
    if (this.closed) return;
    this.trace("session_shutdown", { reason, streams: this.streams.size });
    this.closed = true;
    for (const id of [...this.streams.keys()]) this.closeStream(id, false);
    this.wakeDownlink();
    try { this.ws?.close(1000, "session closed"); } catch {}
    this.ws = null;
    // Do not let a later isolate resurrect a deleted/failed session.
    this.ctx.waitUntil(Promise.resolve(this.ctx.storage.delete("expiresAt")).catch(() => {}));
  }
}

function waitFor(promise, signal, timeout, reason) {
  return new Promise((resolve, reject) => {
    const aborted = () => finish(reject, new Error("stream closed"));
    let timer, settled = false;
    const finish = (settle, value) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      signal.removeEventListener("abort", aborted);
      settle(value);
    };
    // Always attach handlers, even if cancellation already happened.
    Promise.resolve(promise).then(value => finish(resolve, value), error => finish(reject, error));
    if (signal.aborted) return aborted();
    signal.addEventListener("abort", aborted, { once: true });
    timer = setTimeout(() => finish(reject, new Error(reason)), timeout);
  });
}

function ignoreFailure(fn) { try { Promise.resolve(fn()).catch(() => {}); } catch {} }
function safeError(error) { return error instanceof Error ? error.name + ": " + error.message.slice(0, 160) : "I/O error"; }

/* ===== index.js ===== */

export default {
  async fetch(request, env) {
    try {
      return await route(request, env);
    } catch (error) {
      console.error("unhandled request error", error);
      return camouflage();
    }
  },
};

export class WebProxySession extends RelaySession {
  constructor(ctx, env) { super(ctx, env, connect); }
}

async function route(request, env) {
  const url = new URL(request.url);
  const expectedHost = canonicalHost(env.PUBLIC_HOSTNAME || url.hostname);
  if (canonicalHost(url.hostname) !== expectedHost) return camouflage();

  if (url.pathname === "/" && request.method === "GET") {
    const capability = exactBridgeQuery(url);
    const telegram = exactTelegramQuery(url, expectedHost, env.PROXY_SECRET);
    if (!capability && !telegram) {
      return publicPage(expectedHost, env.PROXY_SECRET);
    }
    if (capability && !(await capabilityMatches(capability, expectedHost, env.PROXY_SECRET))) {
      return publicPage(expectedHost, env.PROXY_SECRET);
    }
    const bootstrap = await createBootstrap(env, request.headers.get("CF-Connecting-IP") || "");
    return bridgePage(expectedHost, bootstrap);
  }

  if (url.pathname === "/api/v1/session") {
    if (request.headers.has("Cookie")) return camouflage();
    if (request.method === "DELETE") {
      const token = bearer(request);
      if (!(await verifySessionToken(env, expectedHost, token))) return camouflage();
      const stub = env.SESSIONS.get(env.SESSIONS.idFromName(token));
      await stub.fetch("https://session/internal/close", { method: "POST" });
      return new Response(null, { status: 204, headers: noStore() });
    }
    if (request.method !== "POST" || !isBinary(request.headers.get("Content-Type"))) return camouflage();
    const bootstrap = bearer(request);
    if (!bootstrap || !(await verifyBootstrap(env, bootstrap, request.headers.get("CF-Connecting-IP") || ""))) return camouflage();
    const hello = await readHello(request);
    if (!isHello(hello)) return camouflage();

    const sessionToken = await createSessionToken(env, expectedHost);
    const stub = env.SESSIONS.get(env.SESSIONS.idFromName(sessionToken));
    const init = await stub.fetch("https://session/internal/init", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: "{}",
    });
    if (!init.ok) return camouflage();

    const welcome = encodeFrame(FRAME.WELCOME, 0);
    return new Response(welcome, {
      status: 200,
      headers: {
        ...noStore(),
        "Content-Type": "application/octet-stream",
        "X-Session-Token": sessionToken,
        "X-Carrier-Mode": "websocket",
        "X-Down-Cursor": "0",
      },
    });
  }

  if (url.pathname === "/api/v1/ws" && request.headers.get("Upgrade")?.toLowerCase() === "websocket") {
    const protocols = (request.headers.get("Sec-WebSocket-Protocol") || "").split(",").map((v) => v.trim());
    const protocol = protocols.find((v) => v.startsWith("tproxy-v1."));
    const token = protocol?.slice("tproxy-v1.".length);
    if (!(await verifySessionToken(env, expectedHost, token))) return camouflage();
    const stub = env.SESSIONS.get(env.SESSIONS.idFromName(token));
    return stub.fetch("https://session/internal/ws", {
      headers: { Upgrade: "websocket", "X-TProxy-Protocol": protocol },
    });
  }

  if (url.pathname === "/healthz" && request.method === "GET") {
    return Response.json({ ok: true, carrier: "websocket", relay: "direct-telegram-dc" }, { headers: noStore() });
  }

  return camouflage();
}

function publicPage(host, secret) {
  const safeHost = String(host || "").replace(/[&<>"']/g, "");
  const safeSecret = String(secret || "").replace(/[^0-9a-f]/gi, "").toLowerCase();
  const telegramUrl = `https://t.me/webproxy?server=${encodeURIComponent(safeHost)}&secret=${encodeURIComponent(safeSecret)}`;
  const html = `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="robots" content="noindex,nofollow"><title>TWP-CF Proxy</title><style>
:root{color-scheme:dark;--bg:#0b0e13;--panel:#141a22;--field:#090d12;--line:#29323e;--line2:#3b4858;--text:#e7edf4;--muted:#8793a2;--blue:#4d9fff;--blue2:#79b8ff;--green:#46d98b}
*{box-sizing:border-box}html{background:var(--bg)}body{margin:0;min-height:100vh;background:linear-gradient(180deg,#090c11,#0d1117 50%,#090c11);color:var(--text);font:14px/1.6 ui-monospace,SFMono-Regular,Menlo,Monaco,Consolas,monospace}body:before{content:"";position:fixed;inset:0;pointer-events:none;opacity:.14;background:linear-gradient(rgba(255,255,255,.018) 1px,transparent 1px),linear-gradient(90deg,rgba(255,255,255,.018) 1px,transparent 1px);background-size:32px 32px}
.wrap{width:min(720px,calc(100% - 24px));margin:0 auto;padding:28px 0 38px;position:relative}.top{display:flex;justify-content:space-between;align-items:center;gap:16px;margin-bottom:17px;padding:12px 14px;background:#10151c;border:1px solid var(--line);border-radius:7px;box-shadow:0 11px 30px rgba(0,0,0,.22)}.brand{display:flex;gap:10px;align-items:center}.mark{width:34px;height:34px;display:grid;place-items:center;border:1px solid #354252;border-radius:6px;background:#090d12;color:var(--blue2)}.mark svg{width:18px;height:18px}.brand h1{font-size:15px;margin:0;line-height:1.1}.brand p{font-size:9px;color:var(--muted);margin:4px 0 0}.state{display:flex;align-items:center;gap:6px;color:#94a0af;font-size:9px}.state i{width:6px;height:6px;border-radius:50%;background:var(--green);box-shadow:0 0 8px rgba(70,217,139,.55)}
h2{font-size:17px;margin:17px 0 3px}.intro{color:var(--muted);font-size:10px;margin:0 0 12px}.grid{display:grid;grid-template-columns:1fr 1fr;gap:10px}.card{position:relative;background:var(--panel);border:1px solid var(--line);border-radius:7px;padding:15px;box-shadow:0 12px 32px rgba(0,0,0,.2)}.card:before{content:"";position:absolute;left:-1px;top:9px;bottom:9px;width:2px;border-radius:2px;background:var(--blue);opacity:.72}.wide{grid-column:1/-1}.label{font-size:9px;color:#a9b4c1;text-transform:uppercase;letter-spacing:.05em;margin-bottom:5px}.value{font-size:11px;word-break:break-all}.mono{font:11px/1.55 ui-monospace,SFMono-Regular,Menlo,monospace}.row{display:flex;gap:7px;align-items:center}.row .value{flex:1;min-width:0}.btn{height:32px;border:1px solid var(--line2);background:#0b1016;color:#dce4ed;border-radius:5px;padding:0 10px;font:600 9px ui-monospace,SFMono-Regular,Menlo,monospace;cursor:pointer;text-decoration:none;white-space:nowrap;transition:background .15s,border-color .15s,transform .15s}.btn:hover{background:#121923;border-color:#526174;transform:translateY(-1px)}.btn.primary{background:var(--blue);border-color:var(--blue);color:#06111e;box-shadow:0 5px 15px rgba(77,159,255,.14)}.actions{display:flex;gap:7px;flex-wrap:wrap;margin-top:11px}.note{color:#6e7a89;font-size:8px;margin-top:5px}.footer{text-align:center;color:#5f6b79;font-size:8px;margin-top:17px}.social{display:flex;justify-content:center;gap:14px;margin-bottom:5px}.social a{display:inline-flex;align-items:center;gap:5px;color:#7d8998;text-decoration:none}.social a:hover{color:#dfe8f1}.social svg{width:13px;height:13px}
@keyframes panelIn{from{opacity:0;transform:translateY(5px)}to{opacity:1;transform:none}}.card{animation:panelIn .22s ease both}.card:nth-child(2){animation-delay:.03s}.card:nth-child(3){animation-delay:.06s}.card:nth-child(4){animation-delay:.09s}.card:nth-child(5){animation-delay:.12s}
@media(max-width:620px){.wrap{width:calc(100% - 16px);padding:17px 0 26px}.state{display:none}.grid{grid-template-columns:1fr}.wide{grid-column:auto}.card{padding:13px}.row{align-items:stretch}.row .btn{flex:none}.actions .btn{flex:1}}
</style></head><body><main class="wrap"><header class="top"><div class="brand"><div class="mark"><svg viewBox="0 0 24 24" aria-hidden="true"><path fill="currentColor" d="M21.5 3.2 2.9 10.4c-.9.35-.88 1.62.03 1.94l4.65 1.63 1.74 5.5c.28.88 1.4 1.08 1.97.36l2.55-3.22 4.8 3.52c.78.57 1.9.15 2.1-.8l2.63-14.8c.17-.98-.75-1.68-1.87-1.33ZM9.15 13.42l8.98-5.66-7.07 7.1-.64 2.14-1.27 3.58Zm2.9 4.24.42-1.43 1.03-1.03 1.9 1.39-3.35 1.07Z"/></svg></div><div><h1>TWP-CF</h1><p>Telegram proxy panel</p></div></div><div class="state"><i></i>Online</div></header><h2>Proxy</h2><p class="intro">Your deployed Telegram web proxy is ready.</p><section class="grid"><div class="card"><div class="label">Server</div><div class="value mono">${safeHost}</div></div><div class="card"><div class="label">Port</div><div class="value mono">443</div></div><div class="card wide"><div class="label">Proxy secret</div><div class="row"><div class="value mono" id="secret">${safeSecret}</div><button class="btn" onclick="copyText(secret,this)">Copy</button></div><div class="note">Keep this value private. It authenticates the proxy.</div></div><div class="card wide"><div class="label">Web proxy address</div><div class="row"><div class="value mono" id="proxyAddress">${telegramUrl}</div><button class="btn" onclick="copyText(document.getElementById('proxyAddress').textContent,this)">Copy</button></div><div class="actions"><button class="btn primary" id="openProxy">Open proxy</button><a class="btn" href="/healthz">Health</a></div><div class="note">Use this Telegram Web Proxy address directly. No panel page is required.</div></div></section><div class="footer"><div class="social"><a href="https://github.com/ArasTey" target="_blank" rel="noopener noreferrer"><svg viewBox="0 0 24 24" aria-hidden="true"><path fill="currentColor" d="M12 2C6.48 2 2 6.58 2 12.24c0 4.52 2.87 8.35 6.84 9.7.5.1.68-.23.68-.49v-1.72c-2.78.62-3.37-1.2-3.37-1.2-.46-1.2-1.12-1.52-1.12-1.52-.91-.64.07-.63.07-.63 1 .08 1.53 1.06 1.53 1.06.9 1.59 2.36 1.13 2.94.86.09-.67.35-1.13.64-1.39-2.22-.26-4.56-1.15-4.56-5.08 0-1.12.39-2.03 1.03-2.75 0-.26-.45-1.3.1-2.71 0 0 .84-.28 2.75 1.05A9.2 9.2 0 0 1 12 7.85c.85 0 1.7.12 2.5.37 1.9-1.33 2.74-1.05 2.74-1.05.55 1.41.2 2.45.1 2.71.64.72 1.03 1.63 1.03 2.75 0 3.94-2.35 4.81-4.59 5.07.36.32.68.94.68 1.9v2.82c0 .27.18.6.69.49A10.25 10.25 0 0 0 22 12.24C22 6.58 17.52 2 12 2Z"/></svg>GitHub</a><a href="https://t.me/imArasTey" target="_blank" rel="noopener noreferrer"><svg viewBox="0 0 24 24" aria-hidden="true"><path fill="currentColor" d="M21.5 3.2 2.9 10.4c-.9.35-.88 1.62.03 1.94l4.65 1.63 1.74 5.5c.17-.98-.75-1.68-1.87-1.33ZM9.15 13.42l8.98-5.66-7.07 7.1-.64 2.14-1.27 3.58Zm2.9 4.24.42-1.43 1.03-1.03 1.9 1.39-3.35 1.07Z"/></svg>Telegram</a></div>TWP-CF · Telegram web proxy</div></main><script>const telegram=${JSON.stringify(telegramUrl)};document.getElementById("openProxy").onclick=()=>location.href=telegram;function copyText(value,button){if(!value)return;const done=()=>{const old=button.textContent;button.textContent="Copied";setTimeout(()=>button.textContent=old,900)};if(navigator.clipboard?.writeText){navigator.clipboard.writeText(value).then(done).catch(()=>{})}else{const area=document.createElement("textarea");area.value=value;area.style.position="fixed";area.style.opacity="0";document.body.appendChild(area);area.select();try{document.execCommand("copy");done()}catch{}area.remove()}}</script></body></html>`;
  return new Response(html,{status:200,headers:{"Content-Type":"text/html; charset=utf-8","Cache-Control":"no-store","Content-Security-Policy":"default-src 'none'; style-src 'unsafe-inline'; script-src 'unsafe-inline'; connect-src 'self'; base-uri 'none'; frame-ancestors 'none'"}});
}

function camouflage() {
  return new Response("<!doctype html><meta charset=utf-8><title>Not found</title><h1>Not found</h1>", {
    status: 404,
    headers: { "Content-Type": "text/html; charset=utf-8", "Cache-Control": "no-store" },
  });
}

function exactTelegramQuery(url, host, secret) {
  if (url.searchParams.size !== 2 || !url.searchParams.has("server") || !url.searchParams.has("secret")) return false;
  return canonicalHost(url.searchParams.get("server")) === canonicalHost(host) && url.searchParams.get("secret") === String(secret || "");
}

function exactBridgeQuery(url) {
  if (url.searchParams.size !== 1 || !url.searchParams.has("bridge")) return null;
  const value = url.searchParams.get("bridge");
  return /^[A-Za-z0-9_-]{43}$/.test(value || "") && url.search === `?bridge=${value}` ? value : null;
}

async function capabilityMatches(candidate, host, hexSecret) {
  if (!/^(?:[0-9a-f]{32}|dd[0-9a-f]{32})$/.test(String(hexSecret || ""))) return false;
  const secret = hexToBytes(hexSecret);
  const context = new TextEncoder().encode(`tdesktop-web-proxy-bridge-v1\n${host}`);
  const expected = base64url(await hmac(secret, context));
  return constantTimeEqual(candidate, expected);
}

async function createBootstrap(env, _ip) {
  const ttl = clampInt(env.SESSION_TTL_SECONDS, 30, 600, 300);
  const payload = base64url(new TextEncoder().encode(JSON.stringify({ exp: Math.floor(Date.now() / 1000) + ttl, n: randomToken(16) })));
  const signature = base64url(await hmac(signingKey(env), new TextEncoder().encode(payload)));
  return `${payload}.${signature}`;
}

async function verifyBootstrap(env, token, _ip) {
  const [payload, signature, extra] = token.split(".");
  if (!payload || !signature || extra) return false;
  const expected = base64url(await hmac(signingKey(env), new TextEncoder().encode(payload)));
  if (!constantTimeEqual(signature, expected)) return false;
  try {
    const data = JSON.parse(new TextDecoder().decode(base64urlDecode(payload)));
    return Number.isInteger(data.exp) && data.exp >= Math.floor(Date.now() / 1000);
  } catch { return false; }
}

function signingKey(env) {
  // Domain separation lets one user-supplied proxy secret safely serve both
  // MTProxy authentication and short-lived bootstrap-token signing.
  return new TextEncoder().encode(`twp-cf/session-signing/v1\n${String(env.PROXY_SECRET || "")}`);
}

async function hmac(keyBytes, data) {
  const key = await crypto.subtle.importKey("raw", keyBytes, { name: "HMAC", hash: "SHA-256" }, false, ["sign"]);
  return new Uint8Array(await crypto.subtle.sign("HMAC", key, data));
}

// Keep the opaque 43-character wire format, but reject fabricated credentials
// before they can allocate or address a Durable Object.
async function createSessionToken(env, host) {
  const nonce = crypto.getRandomValues(new Uint8Array(16));
  const mac = await sessionMac(env, host, nonce);
  const bytes = new Uint8Array(32); bytes.set(nonce); bytes.set(mac.subarray(0, 16), 16);
  return base64url(bytes);
}
async function verifySessionToken(env, host, token) {
  if (!/^[A-Za-z0-9_-]{43}$/.test(token || "")) return false;
  const bytes = base64urlDecode(token);
  if (base64url(bytes) !== token) return false;
  const mac = await sessionMac(env, host, bytes.subarray(0, 16));
  return constantTimeEqual(base64url(bytes.subarray(16)), base64url(mac.subarray(0, 16)));
}
function sessionMac(env, host, nonce) {
  const context = new TextEncoder().encode("twp-cf/session-token/v1\n" + host + "\n");
  const bytes = new Uint8Array(context.length + nonce.length); bytes.set(context); bytes.set(nonce, context.length);
  return hmac(signingKey(env), bytes);
}
async function readHello(request) {
  if (!request.body) return new Uint8Array();
  const reader = request.body.getReader(), bytes = new Uint8Array(9);
  let length = 0;
  try {
    for (;;) {
      const { value, done } = await reader.read();
      if (done) return bytes.subarray(0, length);
      if (length + value.length > bytes.length) {
        await reader.cancel(); return new Uint8Array();
      }
      bytes.set(value, length); length += value.length;
    }
  } finally { reader.releaseLock(); }
}

function isHello(bytes) {
  try {
    const frames = parseFrames(bytes);
    return frames.length === 1 && frames[0].type === FRAME.HELLO && frames[0].streamId === 0 && frames[0].payload.length === 1 && frames[0].payload[0] === 1;
  } catch { return false; }
}

function bearer(request) {
  const value = request.headers.get("Authorization") || "";
  return value.startsWith("Bearer ") ? value.slice(7) : "";
}

function isBinary(value) {
  return /^application\/octet-stream(?:\s*;.*)?$/i.test(value || "");
}
function noStore() { return { "Cache-Control": "no-store" }; }
function canonicalHost(value) { return String(value || "").trim().toLowerCase().replace(/\.$/, ""); }
function randomToken(bytes) { const value = new Uint8Array(bytes); crypto.getRandomValues(value); return base64url(value); }
function hexToBytes(hex) { const out = new Uint8Array(hex.length / 2); for (let i = 0; i < out.length; i++) out[i] = Number.parseInt(hex.slice(i * 2, i * 2 + 2), 16); return out; }
function base64url(bytes) { let s = ""; for (let i = 0; i < bytes.length; i += 0x8000) s += String.fromCharCode(...bytes.subarray(i, i + 0x8000)); return btoa(s).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, ""); }
function base64urlDecode(value) { const padded = value.replace(/-/g, "+").replace(/_/g, "/") + "=".repeat((4 - (value.length % 4)) % 4); const raw = atob(padded); return Uint8Array.from(raw, (c) => c.charCodeAt(0)); }
function constantTimeEqual(a, b) { if (a.length !== b.length) return false; let diff = 0; for (let i = 0; i < a.length; i++) diff |= a.charCodeAt(i) ^ b.charCodeAt(i); return diff === 0; }

const _test = { FRAME, encodeFrame, parseFrames, isHello, exactBridgeQuery };

