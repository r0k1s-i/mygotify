/*
 * MyGotify: Spotify for MyGo Music, with audio from YouTube Music
 *
 * Copyright (C) 2026 Sonic Liberation (spotube-plugin-spotify)
 * Copyright (C) 2026 r0k1s-i
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program. If not, see <https://www.gnu.org/licenses/>.
 *
 * Attribution:
 * - Spotify Web Player protocol, TOTP auth, and Pathfinder GraphQL queries
 *   ported from sonic-liberation/spotube-plugin-spotify (AGPL-3.0).
 * - YouTube Music search, VisionOS player stream fetching, and ffmpeg/yt-dlp
 *   audio pipeline adapted from egoist/mygo-music-youtube-music, which states
 *   no license: that part is not covered by the AGPL grant above until its
 *   author licenses it.
 */

const t = host.t;

function fail(code, message) {
  const e = new Error(message);
  e.code = code;
  return e;
}

function cookieValue(cookieStr, name) {
  if (!cookieStr) return "";
  for (const part of cookieStr.split(";")) {
    const at = part.indexOf("=");
    if (at === -1) continue;
    if (part.slice(0, at).trim() === name) return part.slice(at + 1).trim();
  }
  return "";
}

const webUA =
  "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36";
const visionUA =
  "Mozilla/5.0 (Macintosh; Intel Mac OS X 15_7_3) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/26.0 Safari/605.1.15";

// ============================================================================
// Cryptography: Pure JS SHA-1, HMAC-SHA1, Base32, and TOTP (RFC 6238)
// ============================================================================

function sha1Raw(bytes) {
  const totalLen = bytes.length;
  const bitLen = totalLen * 8;
  const paddedLen = Math.ceil((totalLen + 9) / 64) * 64;
  const buf = new Uint8Array(paddedLen);
  buf.set(bytes);
  buf[totalLen] = 0x80;
  const view = new DataView(buf.buffer);
  view.setUint32(paddedLen - 4, bitLen, false);

  let [h0, h1, h2, h3, h4] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];
  const rotl = (x, n) => (x << n) | (x >>> (32 - n));
  const w = new Uint32Array(80);

  for (let at = 0; at < paddedLen; at += 64) {
    for (let i = 0; i < 16; i++) {
      w[i] = view.getUint32(at + i * 4, false);
    }
    for (let i = 16; i < 80; i++) {
      w[i] = rotl(w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16], 1);
    }
    let [a, b, c, d, e] = [h0, h1, h2, h3, h4];
    for (let i = 0; i < 80; i++) {
      let f, k;
      if (i < 20) {
        f = (b & c) | (~b & d);
        k = 0x5a827999;
      } else if (i < 40) {
        f = b ^ c ^ d;
        k = 0x6ed9eba1;
      } else if (i < 60) {
        f = (b & c) | (b & d) | (c & d);
        k = 0x8f1bbcdc;
      } else {
        f = b ^ c ^ d;
        k = 0xca62c1d6;
      }
      const temp = (rotl(a, 5) + f + e + k + w[i]) | 0;
      e = d;
      d = c;
      c = rotl(b, 30);
      b = a;
      a = temp;
    }
    h0 = (h0 + a) | 0;
    h1 = (h1 + b) | 0;
    h2 = (h2 + c) | 0;
    h3 = (h3 + d) | 0;
    h4 = (h4 + e) | 0;
  }
  const out = new Uint8Array(20);
  const outView = new DataView(out.buffer);
  outView.setUint32(0, h0, false);
  outView.setUint32(4, h1, false);
  outView.setUint32(8, h2, false);
  outView.setUint32(12, h3, false);
  outView.setUint32(16, h4, false);
  return out;
}

function hmacSha1(keyBytes, messageBytes) {
  const blockSize = 64;
  let k = keyBytes;
  if (k.length > blockSize) {
    k = sha1Raw(k);
  }
  const paddedKey = new Uint8Array(blockSize);
  paddedKey.set(k);

  const oPad = new Uint8Array(blockSize);
  const iPad = new Uint8Array(blockSize);
  for (let i = 0; i < blockSize; i++) {
    oPad[i] = paddedKey[i] ^ 0x5c;
    iPad[i] = paddedKey[i] ^ 0x36;
  }

  const innerMsg = new Uint8Array(blockSize + messageBytes.length);
  innerMsg.set(iPad, 0);
  innerMsg.set(messageBytes, blockSize);
  const innerHash = sha1Raw(innerMsg);

  const outerMsg = new Uint8Array(blockSize + innerHash.length);
  outerMsg.set(oPad, 0);
  outerMsg.set(innerHash, blockSize);
  return sha1Raw(outerMsg);
}

function base32Decode(str) {
  const alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567";
  const clean = str.toUpperCase().replace(/=+$/, "");
  let bits = 0;
  let value = 0;
  const bytes = [];
  for (let i = 0; i < clean.length; i++) {
    const idx = alphabet.indexOf(clean[i]);
    if (idx === -1) continue;
    value = (value << 5) | idx;
    bits += 5;
    if (bits >= 8) {
      bytes.push((value >>> (bits - 8)) & 0xff);
      bits -= 8;
    }
  }
  return new Uint8Array(bytes);
}

function totp(keyBytes, timeSec, digits = 6, period = 30) {
  const counter = Math.floor(timeSec / period);
  const counterBuf = new Uint8Array(8);
  const view = new DataView(counterBuf.buffer);
  const hi = Math.floor(counter / 0x100000000);
  const lo = counter >>> 0;
  view.setUint32(0, hi, false);
  view.setUint32(4, lo, false);

  const hash = hmacSha1(keyBytes, counterBuf);
  const offset = hash[hash.length - 1] & 0x0f;
  const binary =
    ((hash[offset] & 0x7f) << 24) |
    ((hash[offset + 1] & 0xff) << 16) |
    ((hash[offset + 2] & 0xff) << 8) |
    (hash[offset + 3] & 0xff);
  const mod = 10 ** digits;
  return (binary % mod).toString().padStart(digits, "0");
}

// ============================================================================
// Spotify Authentication & Web Player Token Generation
// ============================================================================

const FALLBACK_NUANCE = {
  s: "GM3TMMJTGYZTQNZVGM4DINJZHA4TGOBYGMZTCMRTGEYDSMJRHE4TEOBUG4YTCMRUGQ4DQOJUGQYTAMRRGA2TCMJSHE3TCMBY",
  v: 61,
};

async function getNuance(bustCache = false) {
  try {
    const url = bustCache
      ? `https://gist.githubusercontent.com/raw/22ed9c6ba463899e933427f7de1f0eef/nuances.json?t=${Date.now()}`
      : "https://gist.githubusercontent.com/raw/22ed9c6ba463899e933427f7de1f0eef/nuances.json";
    const res = await fetch(url);
    if (res.ok) {
      const list = await res.json();
      if (Array.isArray(list) && list.length > 0) {
        return list.reduce((max, item) => (item.v > max.v ? item : max), list[0]);
      }
    }
  } catch (e) {
    console.warn("nuance fetch error:", e.message);
  }
  return FALLBACK_NUANCE;
}

async function getServerTime() {
  try {
    const res = await fetch("https://open.spotify.com/api/server-time");
    if (res.ok) {
      const data = await res.json();
      if (data.serverTime) return Number(data.serverTime);
    }
  } catch (e) {
    console.warn("server-time fetch error:", e.message);
  }
  return Math.floor(Date.now() / 1000);
}

let tokenInfo = null;

async function requestToken(spDc = "", bustNuance = false) {
  const nuance = await getNuance(bustNuance);
  const serverTime = await getServerTime();
  const keyBytes = base32Decode(nuance.s);
  const otp = totp(keyBytes, serverTime);

  const tokenUrl = `https://open.spotify.com/api/token?reason=transport&productType=web-player&totp=${otp}&totpServer=${otp}&totpVer=${nuance.v}`;
  const headers = { "User-Agent": webUA };
  if (spDc) {
    headers["Cookie"] = `sp_dc=${spDc};`;
  }
  const res = await fetch(tokenUrl, { headers });
  if (!res.ok) {
    if (!bustNuance) {
      return requestToken(spDc, true);
    }
    throw new Error(`Spotify token error: ${res.status}`);
  }
  const data = await res.json();
  return {
    accessToken: data.accessToken,
    clientId: data.clientId || "d8a5ed958d274c2e8ee717e6a4b0971d",
    expiresAt: data.accessTokenExpirationTimestampMs || Date.now() + 3600000,
    isAnonymous: Boolean(data.isAnonymous),
    spDc,
  };
}

async function getToken() {
  const spDc = host.storage.get("sp_dc") || "";
  const now = Date.now();
  // Check memory token
  if (tokenInfo && tokenInfo.spDc === spDc && tokenInfo.expiresAt - now > 60000) {
    return tokenInfo.accessToken;
  }
  // Check persisted storage
  const stored = host.storage.get("token");
  if (stored && stored.spDc === spDc && stored.expiresAt - now > 60000) {
    tokenInfo = stored;
    return tokenInfo.accessToken;
  }
  tokenInfo = await requestToken(spDc);
  host.storage.set("token", tokenInfo);
  return tokenInfo.accessToken;
}

let clientTokenInfo = null;

async function requestClientToken(clientId = "d8a5ed958d274c2e8ee717e6a4b0971d") {
  const res = await fetch("https://clienttoken.spotify.com/v1/clienttoken", {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      Accept: "application/json",
      "User-Agent": webUA,
    },
    body: JSON.stringify({
      client_data: {
        client_id: clientId,
        client_version: "1.2.52.442.g0189348d",
        js_sdk_data: {
          device_brand: "Apple",
          device_model: "unknown",
          os: "Mac OS",
          os_version: "10.15.7",
        },
      },
    }),
  });
  if (!res.ok) {
    throw new Error(`Spotify client token error: ${res.status}`);
  }
  const data = await res.json();
  const token = data.granted_token?.token || "";
  const expiresAfter = data.granted_token?.expires_after_seconds || 1200000;
  return {
    clientToken: token,
    expiresAt: Date.now() + expiresAfter * 1000,
  };
}

async function getClientToken(clientId) {
  const now = Date.now();
  if (clientTokenInfo && clientTokenInfo.expiresAt - now > 60000) {
    return clientTokenInfo.clientToken;
  }
  const stored = host.storage.get("client_token");
  if (stored && stored.expiresAt - now > 60000) {
    clientTokenInfo = stored;
    return clientTokenInfo.clientToken;
  }
  clientTokenInfo = await requestClientToken(clientId);
  host.storage.set("client_token", clientTokenInfo);
  return clientTokenInfo.clientToken;
}

// ============================================================================
// Spotify Pathfinder GraphQL Client
// ============================================================================

async function gql(operationName, sha256Hash, variables = {}) {
  let token = await getToken();
  const spDc = host.storage.get("sp_dc");
  const headers = {
    "Content-Type": "application/json",
    Accept: "application/json",
    Authorization: `Bearer ${token}`,
    "User-Agent": webUA,
  };
  if (spDc) {
    headers["Cookie"] = `sp_dc=${spDc}`;
  }
  let res = await fetch("https://api-partner.spotify.com/pathfinder/v2/query", {
    method: "POST",
    headers,
    body: JSON.stringify({
      operationName,
      variables,
      extensions: {
        persistedQuery: {
          version: 1,
          sha256Hash,
        },
      },
    }),
  });

  if (res.status === 401) {
    // Retry once with refreshed token
    tokenInfo = null;
    host.storage.remove("token");
    token = await getToken();
    headers["Authorization"] = `Bearer ${token}`;
    res = await fetch("https://api-partner.spotify.com/pathfinder/v2/query", {
      method: "POST",
      headers,
      body: JSON.stringify({
        operationName,
        variables,
        extensions: {
          persistedQuery: {
            version: 1,
            sha256Hash,
          },
        },
      }),
    });
    if (res.status === 401) {
      if (spDc) {
        signOut();
        throw fail("signIn", t("Your Spotify session has ended: sign in again"));
      }
    }
  }

  if (!res.ok) {
    throw new Error(`Spotify GQL ${operationName}: ${res.status}`);
  }
  return res.json();
}

// ============================================================================
// Data Transformation & Model Mappers
// ============================================================================

function cleanDescription(text) {
  if (!text) return "";
  return text
    .replace(/<[^>]*>/g, "")
    .replace(/&#x27;/g, "'")
    .replace(/&quot;/g, '"')
    .replace(/&amp;/g, "&")
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .trim();
}

function imageOf(node) {
  if (!node) return undefined;
  const list = node.sources || (node.items && node.items[0]?.sources) || [];
  if (!list.length) return undefined;
  const sorted = [...list].sort((a, b) => (b.width || 0) - (a.width || 0));
  return sorted[0]?.url;
}

function toArtist(raw) {
  if (!raw) return { id: "", name: "" };
  const id = raw.uri ? raw.uri.replace(/^spotify:artist:/, "") : raw.id || "";
  const name = raw.profile?.name || raw.name || "";
  const imageUrl = imageOf(raw.visuals?.avatarImage || raw.images);
  return {
    id,
    name,
    imageUrl,
    following: Boolean(raw.following ?? raw.saved),
  };
}

function toAlbum(raw, fallbackArtists = []) {
  if (!raw) return { id: "", name: "" };
  const id = raw.uri ? raw.uri.replace(/^spotify:album:/, "") : raw.id || "";
  const name = raw.name || "";
  const imageUrl = imageOf(raw.coverArt || raw.images);
  const rawArtists = (raw.artists?.items || []).map(toArtist);
  const artists = rawArtists.length > 0 ? rawArtists : fallbackArtists;
  const released = raw.date?.isoString || (raw.date?.year ? String(raw.date.year) : "");
  return {
    id,
    name,
    imageUrl,
    artists,
    released,
    saved: Boolean(raw.saved),
  };
}

// A track wrapped as {_uri, data}, as liked songs and the home page give it,
// may have its URI only on the wrapper.
const unwrap = (w) => (w?.data ? { uri: w._uri, ...w.data } : null);

function toTrack(raw, fallbackAlbum = null) {
  if (!raw) return { id: "", name: "", album: { id: "", name: "" }, duration: 0 };
  const id = raw.uri ? raw.uri.replace(/^spotify:track:/, "") : raw.id || "";
  const name = raw.name || "";
  const artists = (raw.artists?.items || [...(raw.firstArtist?.items || []), ...(raw.otherArtists?.items || [])]).map(toArtist);
  const album = raw.albumOfTrack ? toAlbum(raw.albumOfTrack) : fallbackAlbum || { id: "", name: "" };
  // Playlists, and so the home page and radio, name it trackDuration. Without
  // it the app can't seek, as the MP3 it's served is live and has no length.
  const duration = raw.duration?.totalMilliseconds || raw.trackDuration?.totalMilliseconds || 0;
  const url = raw.sharingInfo?.shareUrl || (id ? `https://open.spotify.com/track/${id}` : "");
  return {
    id,
    name,
    artists,
    album,
    duration,
    url,
  };
}

function toPlaylist(raw, tracks = []) {
  if (!raw) return { id: "", name: "" };
  const id = raw.uri ? raw.uri.replace(/^spotify:playlist:/, "") : raw.id || "";
  const name = raw.name || "";
  const imageUrl = imageOf(raw.images);
  const description = cleanDescription(raw.description);
  const owner = raw.ownerV2?.data?.name || raw.ownerV2?.data?.username || "";
  const trackCount = raw.content?.totalCount || tracks.length;
  return {
    id,
    name,
    imageUrl,
    description,
    owner,
    trackCount,
    tracks,
  };
}

// ============================================================================
// Plugin Exports: Authentication & User Account
// ============================================================================

// The sp_dc cookie pasted in the settings, as its value or as "sp_dc=…".
function pastedSpDc() {
  const pasted = (host.setting("spDc") || "").trim();
  return pasted.includes("=") ? cookieValue(pasted, "sp_dc") : pasted;
}

// Signing in takes the cookie from the settings when one is pasted there.
// Otherwise it's Spotify's page in a window of the app, except on Linux, where
// opening that window from a plugin aborts the app (WebKitGTK binds its UI
// thread to whichever thread first uses it), so the settings are the only way.
export async function signIn() {
  let spDc = pastedSpDc();
  let cookieHeader = spDc ? `sp_dc=${spDc}` : "";
  if (!spDc) {
    if (host.platform === "linux") {
      throw fail("setup", t("Paste your sp_dc cookie in the settings to sign in"));
    }
    ({ cookie: cookieHeader } = await host.webSignIn({
      url: "https://accounts.spotify.com/en/login",
      cookiesOf: "https://open.spotify.com",
      until: ["sp_dc"],
    }));
    spDc = cookieValue(cookieHeader, "sp_dc");
  }
  if (!spDc) {
    throw fail("signIn", t("Spotify didn't take that sign-in: try again"));
  }
  host.storage.set("sp_dc", spDc);
  host.storage.set("cookie", cookieHeader);
  tokenInfo = null;
  host.storage.remove("token");
  const acc = await account().catch(() => null);
  if (!acc) {
    signOut();
    throw fail("signIn", t("Spotify didn't take that sign-in: try again"));
  }
  return acc;
}

// A new cookie in the settings ends the session made with the old one: signing
// in again takes the new one.
export function setSetting({ key }) {
  if (key === "spDc") signOut();
}

export function signOut() {
  host.storage.remove("sp_dc");
  host.storage.remove("cookie");
  host.storage.remove("token");
  host.storage.remove("client_token");
  tokenInfo = null;
  clientTokenInfo = null;
}

export async function account() {
  const spDc = host.storage.get("sp_dc");
  if (!spDc) return null;
  try {
    const res = await gql("profileAttributes", "53bcb064f6cd18c23f752bc324a791194d20df612d8e1239c735144ab0399ced", {});
    const profile = res?.data?.me?.profile;
    if (!profile) return null;
    return {
      id: profile.uri ? profile.uri.replace(/^spotify:user:/, "") : profile.username,
      name: profile.name || profile.username,
      imageUrl: imageOf(profile.avatar),
      page: "me",
    };
  } catch (e) {
    console.warn("account query failed:", e.message);
    return null;
  }
}

// ============================================================================
// Plugin Exports: Home & Browse
// ============================================================================

// The home page's tracks come without their length, which the app needs to
// seek in the live MP3 they're played as. Each is asked for a few at a time,
// and kept, as a track's length doesn't change. api.spotify.com's batch of
// tracks would be one request, but it turns the web player's token away.
async function fillDurations(tracks) {
  const known = host.storage.get("durations") || {};
  const missing = tracks.filter((tr) => !tr.duration && !known[tr.id] && tr.id);
  for (let i = 0; i < missing.length; i += 5) {
    await Promise.all(
      missing.slice(i, i + 5).map(async (tr) => {
        try {
          const res = await gql("getTrack", "612585ae06ba435ad26369870deaae23b5c8800a256cd8a57e08eddc25a37294", {
            uri: `spotify:track:${tr.id}`,
          });
          const ms = res?.data?.trackUnion?.duration?.totalMilliseconds;
          if (ms) known[tr.id] = ms;
        } catch (e) {
          console.warn(`length of ${tr.id}: ${e.message}`);
        }
      })
    );
  }
  if (missing.length) host.storage.set("durations", known);
  for (const tr of tracks) tr.duration = tr.duration || known[tr.id] || 0;
}

export async function home() {
  const spT = cookieValue(host.storage.get("cookie") || "", "sp_t");
  const res = await gql("home", "3357ffed7961629ba92b4e0a41514e4d5004a14355c964c23ce442205c9e44a1", {
    timeZone: "UTC",
    sp_t: spT,
    facet: "",
    sectionItemsLimit: 20,
  });
  const rawSections = res?.data?.home?.sectionContainer?.sections?.items || [];
  const sections = [];
  for (const s of rawSections) {
    const title = s.data?.title?.transformedLabel || s.data?.title?.text;
    if (!title) continue;
    const items = s.sectionItems?.items || [];
    const sec = {
      title,
      tracks: [],
      albums: [],
      artists: [],
      playlists: [],
    };
    for (const it of items) {
      const c = it.content;
      if (!c || !c.data) continue;
      switch (c.__typename) {
        case "TrackResponseWrapper":
          sec.tracks.push(toTrack(unwrap(c)));
          break;
        case "AlbumResponseWrapper":
          sec.albums.push(toAlbum(c.data));
          break;
        case "ArtistResponseWrapper":
          sec.artists.push(toArtist(c.data));
          break;
        case "PlaylistResponseWrapper":
          sec.playlists.push(toPlaylist(c.data));
          break;
      }
    }
    if (sec.tracks.length || sec.albums.length || sec.artists.length || sec.playlists.length) {
      sections.push(sec);
    }
  }
  await fillDurations(sections.flatMap((s) => s.tracks || []));
  return { title: t("Home"), sections };
}

// The home page's shelves of mixes made for the listener: the Daily Mixes,
// Discover Weekly and Release Radar, then their top mixes.
const madeForYouShelves = ["spotify:section:0JQ5DAUnp4wcj0bCb3wh3S", "spotify:section:0JQ5DAnM3wGh0gz1MXnu89"];

async function madeForYou() {
  const shelves = await Promise.allSettled(madeForYouShelves.map((uri) => browse({ page: uri })));
  const sections = shelves.flatMap((shelf) => (shelf.status === "fulfilled" ? shelf.value.sections : []));
  const failed = shelves.find((shelf) => shelf.status === "rejected");
  if (!sections.length && failed) throw failed.reason;
  return { title: t("Made For You"), sections };
}

// What was played here, newest first. Spotify's own history has only what its
// apps played, and these songs never reach it.
const historyLength = 50;

function remember(id) {
  const history = (host.storage.get("history") || []).filter((h) => h !== id);
  history.unshift(id);
  host.storage.set("history", history.slice(0, historyLength));
}

// Each song is asked for once and kept for as long as it's in the history.
async function recentlyPlayed() {
  const history = host.storage.get("history") || [];
  const old = host.storage.get("historyTracks") || {};
  const kept = {};
  for (const id of history) if (old[id]) kept[id] = old[id];
  const missing = history.filter((id) => !kept[id]);
  for (let i = 0; i < missing.length; i += 5) {
    await Promise.all(
      missing.slice(i, i + 5).map(async (id) => {
        try {
          const res = await gql("getTrack", "612585ae06ba435ad26369870deaae23b5c8800a256cd8a57e08eddc25a37294", {
            uri: `spotify:track:${id}`,
          });
          if (res?.data?.trackUnion) kept[id] = toTrack(res.data.trackUnion);
        } catch (e) {
          console.warn(`recently played ${id}: ${e.message}`);
        }
      })
    );
  }
  host.storage.set("historyTracks", kept);
  const tracks = history.map((id) => kept[id]).filter(Boolean);
  return { title: t("Recently Played"), sections: [{ tracks, empty: t("Songs you play will show here") }] };
}

// The listener's own page, from the account menu. The app loads it anew each
// time it's opened, unlike the sidebar's pages, so it's where what was just
// played shows at once.
async function myPage() {
  const me = await account();
  if (!me) throw fail("signIn");
  const [recent, artists] = await Promise.allSettled([recentlyPlayed(), followedArtists()]);
  const sections = [];
  if (recent.status === "fulfilled") {
    sections.push({ ...recent.value.sections[0], title: t("Recently Played"), morePage: "recent" });
  }
  if (artists.status === "fulfilled") {
    sections.push({ ...artists.value.sections[0], title: t("Artists"), morePage: "artists" });
  }
  return { title: me.name, imageUrl: me.imageUrl, sections };
}

export async function browse({ page }) {
  if (!page) return home();
  if (page === "artists") return followedArtists();
  if (page === "madeForYou") return madeForYou();
  if (page === "recent") return recentlyPlayed();
  if (page === "me") return myPage();
  const spT = cookieValue(host.storage.get("cookie") || "", "sp_t");
  const uri = page.startsWith("spotify:") ? page : `spotify:section:${page}`;
  const res = await gql("homeSection", "d62af2714f2623c923cc9eeca4b9545b4363abaa9188a9e94e2b63b823419a2c", {
    uri,
    timeZone: "UTC",
    sp_t: spT,
    sectionItemsOffset: 0,
    sectionItemsLimit: 50,
  });
  const first = res?.data?.homeSections?.sections?.[0];
  if (!first || first.__typename === "NotFound") {
    throw fail("unavailable", t("no such page"));
  }
  const title = first.data?.title?.transformedLabel || t("Browse");
  const items = first.sectionItems?.items || [];
  const sec = { title, tracks: [], albums: [], artists: [], playlists: [] };
  for (const it of items) {
    const c = it.content;
    if (!c || !c.data) continue;
    switch (c.__typename) {
      case "TrackResponseWrapper":
        sec.tracks.push(toTrack(unwrap(c)));
        break;
      case "AlbumResponseWrapper":
        sec.albums.push(toAlbum(c.data));
        break;
      case "ArtistResponseWrapper":
        sec.artists.push(toArtist(c.data));
        break;
      case "PlaylistResponseWrapper":
        sec.playlists.push(toPlaylist(c.data));
        break;
    }
  }
  await fillDurations(sec.tracks);
  return { title, sections: [sec] };
}

// ============================================================================
// Plugin Exports: Catalog Search
// ============================================================================

export async function search({ query, kind, offset = 0 }) {
  const limit = 20;
  switch (kind) {
    case "tracks": {
      const res = await gql("searchTracks", "bc1ca2fcd0ba1013a0fc88e6cc4f190af501851e3dafd3e1ef85840297694428", {
        searchTerm: query,
        offset,
        limit,
        includePreReleases: false,
        numberOfTopResults: 20,
        includeAudiobooks: true,
        includeAuthors: false,
      });
      const data = res?.data?.searchV2?.tracksV2;
      const items = (data?.items || [])
        .filter((it) => it.item?.__typename === "TrackResponseWrapper" && it.item?.data)
        .map((it) => toTrack(it.item.data));
      const total = data?.totalCount || 0;
      return { tracks: items, more: offset + items.length < total };
    }
    case "albums": {
      const res = await gql("searchAlbums", "a71d2c993fc98e1c880093738a55a38b57e69cc4ce5a8c113e6c5920f9513ee2", {
        searchTerm: query,
        offset,
        limit,
        includePreReleases: false,
        numberOfTopResults: 20,
        includeAudiobooks: true,
        includeAuthors: false,
      });
      const data = res?.data?.searchV2?.albumsV2;
      const items = (data?.items || [])
        .filter((it) => it.data)
        .map((it) => toAlbum(it.data));
      const total = data?.totalCount || 0;
      return { albums: items, more: offset + items.length < total };
    }
    case "artists": {
      const res = await gql("searchArtists", "0e6f9020a66fe15b93b3bb5c7e6484d1d8cb3775963996eaede72bac4d97e909", {
        searchTerm: query,
        offset,
        limit,
        includePreReleases: false,
        numberOfTopResults: 20,
        includeAudiobooks: true,
        includeAuthors: false,
      });
      const data = res?.data?.searchV2?.artists;
      const items = (data?.items || [])
        .filter((it) => it.data)
        .map((it) => toArtist(it.data));
      const total = data?.totalCount || 0;
      return { artists: items, more: offset + items.length < total };
    }
    case "playlists": {
      const res = await gql("searchPlaylists", "fc3a690182167dbad20ac7a03f842b97be4e9737710600874cb903f30112ad58", {
        searchTerm: query,
        offset,
        limit,
        includePreReleases: false,
        numberOfTopResults: 20,
        includeAudiobooks: true,
        includeAuthors: false,
      });
      const data = res?.data?.searchV2?.playlists;
      const items = (data?.items || [])
        .filter((it) => it.data)
        .map((it) => toPlaylist(it.data));
      const total = data?.totalCount || 0;
      return { playlists: items, more: offset + items.length < total };
    }
    default:
      return { [kind]: [], more: false };
  }
}

// ============================================================================
// Plugin Exports: Album, Artist, and Playlist Pages
// ============================================================================

export async function album({ id }) {
  const uri = `spotify:album:${id}`;
  const res = await gql("getAlbum", "b9bfabef66ed756e5e13f68a942deb60bd4125ec1f1be8cc42769dc0259b4b10", {
    uri,
    locale: "",
    offset: 0,
    limit: 50,
  });
  const albumData = res?.data?.albumUnion;
  if (!albumData) throw fail("unavailable", t("album not found"));
  const a = toAlbum(albumData);
  const trackItems = albumData.tracksV2?.items || [];
  const tracks = trackItems.map((item) => toTrack(item.track, a));
  return { album: a, tracks };
}

async function fetchDiscographyGroup(opName, groupName, artistUri) {
  const items = [];
  let offset = 0;
  const limit = 100;
  while (true) {
    const res = await gql(opName, "5e07d323febb57b4a56a42abbf781490e58764aa45feb6e3dc0591564fc56599", {
      uri: artistUri,
      offset,
      limit,
    });
    const group = res?.data?.artistUnion?.discography?.[groupName];
    const pageItems = group?.items || [];
    for (const item of pageItems) {
      const rel = item.releases?.items?.[0];
      if (rel?.uri) items.push(rel);
    }
    offset += pageItems.length;
    const totalCount = group?.totalCount ?? 0;
    if (pageItems.length === 0 || offset >= totalCount || pageItems.length < limit) {
      break;
    }
  }
  return items;
}

async function mapConcurrent(items, fn, concurrency = 8) {
  const results = new Array(items.length);
  let index = 0;
  const workers = new Array(Math.min(concurrency, items.length)).fill(null).map(async () => {
    while (index < items.length) {
      const i = index++;
      results[i] = await fn(items[i]).catch(() => null);
    }
  });
  await Promise.all(workers);
  return results;
}

function songKey(name, artists) {
  const tKey = (name || "").trim().toLowerCase();
  const aKey = (artists || []).map((a) => a.id || a.name?.toLowerCase() || "").sort().join(",");
  return `${tKey}::${aKey}`;
}

export async function artist({ id }) {
  const uri = `spotify:artist:${id}`;
  const res = await gql("queryArtistOverview", "7f86ff63e38c24973a2842b672abe44c910c1973978dc8a4a0cb648edef34527", {
    uri,
    locale: "",
    preReleaseV2: false,
  });
  const artistData = res?.data?.artistUnion;
  if (!artistData) throw fail("unavailable", t("artist not found"));
  const art = toArtist(artistData);
  const topTracks = (artistData.discography?.topTracks?.items || []).map((item) => toTrack(item.track));

  // Spotify categorizes discography into albums, singles & EPs, and compilations.
  // Query all three groups concurrently with pagination.
  const [albumReleases, singleReleases, compilationReleases] = await Promise.all([
    fetchDiscographyGroup("queryArtistDiscographyAlbums", "albums", uri).catch(() => []),
    fetchDiscographyGroup("queryArtistDiscographySingles", "singles", uri).catch(() => []),
    fetchDiscographyGroup("queryArtistDiscographyCompilations", "compilations", uri).catch(() => []),
  ]);

  const allReleases = [...albumReleases, ...singleReleases, ...compilationReleases];
  let albums;
  if (allReleases.length === 0) {
    albums = (artistData.discography?.popularReleasesAlbums?.items || []).map((item) => toAlbum(item, [art]));
  } else {
    albums = allReleases.map((rel) => toAlbum(rel, [art]));
  }

  const albumMap = new Map();
  for (const a of albums) {
    if (a.id) albumMap.set(a.id, a);
  }

  // Fetch release tracks with bounded concurrency. For prolific artists with
  // hundreds of releases, cap track fetching to the first 150 releases (albums,
  // then singles) to avoid slow page loads and rate limiting.
  const trackReleases = allReleases.slice(0, 150);
  const releaseTrackItems = await mapConcurrent(
    trackReleases,
    async (rel) => {
      const trackRes = await gql("queryAlbumTracks", "0b6ce3511e1b02e4a40fa95440f992acbe85080eb308af9194322d708fc1914f", {
        uri: rel.uri,
        offset: 0,
        limit: 100,
      });
      return trackRes?.data?.albumUnion?.tracksV2?.items || [];
    },
    8
  );

  const seenTrackIds = new Set();
  const seenSongKeys = new Set();
  const tracks = [];

  // Top 10 tracks first, preserving their exact order
  for (const track of topTracks) {
    if (!track.id) continue;
    if (albumMap.has(track.album.id)) {
      const match = albumMap.get(track.album.id);
      track.album = { ...match, ...track.album, name: match.name || track.album.name };
    }
    seenTrackIds.add(track.id);
    seenSongKeys.add(songKey(track.name, track.artists));
    tracks.push(track);
  }

  // Discography tracks: albums first, then singles & EPs, then compilations.
  // Deduplicate by track ID and by same title + artists (keeping album version
  // over single re-releases). Filter out tracks not by this artist.
  for (let i = 0; i < trackReleases.length; i++) {
    const albumObj = albums[i];
    const items = releaseTrackItems[i] || [];
    for (const item of items) {
      const rawTrack = item.track;
      if (!rawTrack) continue;
      const track = toTrack(rawTrack, albumObj);
      if (!track.id) continue;
      if (!track.artists?.some((a) => a.id === id)) continue;
      if (seenTrackIds.has(track.id)) continue;
      const key = songKey(track.name, track.artists);
      if (seenSongKeys.has(key)) continue;

      seenTrackIds.add(track.id);
      seenSongKeys.add(key);
      tracks.push(track);
    }
  }

  return { artist: art, tracks, albums };
}

export async function playlist({ id }) {
  const uri = `spotify:playlist:${id}`;
  const res = await gql("fetchPlaylist", "cd2275433b29f7316176e7b5b5e098ae7744724e1a52d63549c76636b3257749", {
    uri,
    offset: 0,
    limit: 100,
    enableWatchFeedEntrypoint: true,
  });
  const plData = res?.data?.playlistV2;
  if (!plData) throw fail("unavailable", t("playlist not found"));
  const items = plData.content?.items || [];
  const tracks = items
    .filter((item) => item.itemV2?.__typename === "TrackResponseWrapper" && item.itemV2?.data?.__typename === "Track")
    .map((item) => toTrack(item.itemV2.data));
  return toPlaylist(plData, tracks);
}

// ============================================================================
// Plugin Exports: User Library (Playlists, Liked Songs, Saves)
// ============================================================================

export async function playlists() {
  const spDc = host.storage.get("sp_dc");
  if (!spDc) return [];
  const res = await gql("libraryV3", "390c78e5b951029bad359785e69b07b536a509c581cbcd0aded5e5067f187455", {
    filters: ["Playlists"],
    limit: 50,
    offset: 0,
    flatten: true,
    expandedFolders: [],
    folderUri: null,
    includeFoldersWhenFlattening: true,
  });
  const items = res?.data?.me?.libraryV3?.items || [];
  const out = [];
  for (const libItem of items) {
    if (libItem.item?.__typename === "PlaylistResponseWrapper" && libItem.item?.data) {
      out.push(toPlaylist(libItem.item.data));
    }
  }
  return out;
}

// The artists you follow, for the Artists page of the sidebar. The app has no
// library export for them, so they come as a browse page.
async function followedArtists() {
  const spDc = host.storage.get("sp_dc");
  if (!spDc) throw fail("signIn");
  const limit = 50;
  const artists = [];
  for (let offset = 0; ; offset += limit) {
    const res = await gql("libraryV3", "390c78e5b951029bad359785e69b07b536a509c581cbcd0aded5e5067f187455", {
      filters: ["Artists"],
      limit,
      offset,
      flatten: true,
      expandedFolders: [],
      folderUri: null,
      includeFoldersWhenFlattening: true,
    });
    const lib = res?.data?.me?.libraryV3;
    const items = lib?.items || [];
    for (const libItem of items) {
      if (libItem.item?.__typename === "ArtistResponseWrapper" && libItem.item?.data) {
        artists.push({ ...toArtist(libItem.item.data), following: true });
      }
    }
    if (items.length < limit || offset + limit >= (lib?.totalCount || 0)) break;
  }
  return { title: t("Artists"), sections: [{ artists }] };
}

export async function savedAlbums({ offset = 0 }) {
  const spDc = host.storage.get("sp_dc");
  if (!spDc) throw fail("signIn");
  const limit = 50;
  const res = await gql("libraryV3", "390c78e5b951029bad359785e69b07b536a509c581cbcd0aded5e5067f187455", {
    filters: ["Albums"],
    limit,
    offset,
    flatten: true,
    expandedFolders: [],
    folderUri: null,
    includeFoldersWhenFlattening: true,
  });
  const lib = res?.data?.me?.libraryV3;
  const items = lib?.items || [];
  const albums = items
    .filter((libItem) => libItem.item?.__typename === "AlbumResponseWrapper" && libItem.item?.data)
    .map((libItem) => ({ ...toAlbum(libItem.item.data), saved: true }));
  return { albums, more: offset + items.length < (lib?.totalCount || 0) };
}

export async function liked({ offset = 0 }) {
  const spDc = host.storage.get("sp_dc");
  if (!spDc) throw fail("signIn");
  const limit = 50;
  const res = await gql("fetchLibraryTracks", "087278b20b743578a6262c2b0b4bcd20d879c503cc359a2285baf083ef944240", {
    offset,
    limit,
  });
  const lib = res?.data?.me?.library?.tracks;
  if (!lib) return { tracks: [], more: false };
  const items = lib.items || [];
  const tracks = items.map((item) => toTrack(unwrap(item.track)));
  const total = lib.totalCount || 0;
  return { tracks, more: offset + tracks.length < total };
}

export async function isLiked({ ids }) {
  const spDc = host.storage.get("sp_dc");
  if (!spDc || !ids.length) return Object.fromEntries(ids.map((id) => [id, false]));
  const uris = ids.map((id) => `spotify:track:${id}`);
  const res = await gql("isCurated", "e4ed1f91a2cc5415befedb85acf8671dc1a4bf3ca1a5b945a6386101a22e28a6", { uris });
  const lookup = res?.data?.lookup || [];
  const out = {};
  ids.forEach((id, i) => {
    out[id] = lookup[i]?.data?.isCurated || false;
  });
  return out;
}

export async function like({ id, on }) {
  const spDc = host.storage.get("sp_dc");
  if (!spDc) throw fail("signIn");
  const uri = `spotify:track:${id}`;
  if (on) {
    await gql("addToLibrary", "a3c1ff58e6a36fec5fe1e3a193dc95d9071d96b9ba53c5ba9c1494fb1ee73915", {
      uris: [uri],
    });
  } else {
    await gql("applyCurations", "05b739a3a73091c213385233b9d3ed8a857c2ca29d2eebadb3d04ed12e288697", {
      input: {
        curations: [
          {
            contextUri: "spotify:collection:tracks",
            curationType: "UNCURATE",
          },
        ],
        itemUris: [uri],
      },
    });
  }
}

export async function saveAlbum({ id, on }) {
  const spDc = host.storage.get("sp_dc");
  if (!spDc) throw fail("signIn");
  const uri = `spotify:album:${id}`;
  if (on) {
    await gql("addToLibrary", "a3c1ff58e6a36fec5fe1e3a193dc95d9071d96b9ba53c5ba9c1494fb1ee73915", {
      uris: [uri],
    });
  } else {
    await gql("removeFromLibrary", "a3c1ff58e6a36fec5fe1e3a193dc95d9071d96b9ba53c5ba9c1494fb1ee73915", {
      uris: [uri],
    });
  }
}

export async function followArtist({ id, on }) {
  const spDc = host.storage.get("sp_dc");
  if (!spDc) throw fail("signIn");
  const uri = `spotify:artist:${id}`;
  if (on) {
    await gql("addToLibrary", "a3c1ff58e6a36fec5fe1e3a193dc95d9071d96b9ba53c5ba9c1494fb1ee73915", {
      uris: [uri],
    });
  } else {
    await gql("removeFromLibrary", "a3c1ff58e6a36fec5fe1e3a193dc95d9071d96b9ba53c5ba9c1494fb1ee73915", {
      uris: [uri],
    });
  }
}

export async function savePlaylist({ id, on }) {
  const spDc = host.storage.get("sp_dc");
  if (!spDc) throw fail("signIn");
  const uri = `spotify:playlist:${id}`;
  if (on) {
    await gql("addItemsToRootlist", "bd9c5cae1ee80ebca05d7ed12fd394216f49a20ce72d9dc762868df0f14522ea", {
      uris: [uri],
    });
  } else {
    await gql("removeItemsFromRootlist", "3422f1866532820a1d8d0560f88542dbdbd35d0377ee5ecd49593590f5f1e86b", {
      uris: [uri],
    });
  }
}

// ============================================================================
// Plugin Exports: Radio & Stations
// ============================================================================

const radioStation = {
  id: "radio",
  name: "Radio",
  description: "Songs like the one you played last.",
};

export function stations() {
  return [radioStation];
}

export function played({ id }) {
  host.storage.set("lastPlayed", id);
  remember(id);
}

export async function stationNext() {
  let seed = host.storage.get("lastPlayed");
  if (!seed) {
    const h = await home();
    seed = h.sections.flatMap((s) => s.tracks)[0]?.id;
    if (!seed) return [];
  }
  const token = await getToken();
  const url = `https://spclient.wg.spotify.com/inspiredby-mix/v2/seed_to_playlist/spotify:track:${seed}?response-format=json`;
  const res = await fetch(url, {
    headers: {
      Authorization: `Bearer ${token}`,
      "User-Agent": webUA,
    },
  });
  if (!res.ok) return [];
  const data = await res.json();
  const playlistUri = data.mediaItems?.[0]?.uri;
  if (!playlistUri) return [];
  const pl = await playlist({ id: playlistUri.replace(/^spotify:playlist:/, "") });
  return (pl.tracks || []).filter((tr) => tr.id !== seed);
}

// ============================================================================
// Plugin Exports: Lyrics
// ============================================================================

function normLyricText(text) {
  if (!text) return "";
  return text.toLowerCase().replace(/[^\p{L}\p{N}]/gu, "");
}

function stripTitleNoise(title) {
  return (title || "")
    .replace(/\s*[\(\[](?:feat\.?|featuring|with|remaster\w*|\d{4}\s+remaster\w*|live|deluxe|version|ver\.|bonus|from\s+|唱片版|remix).*?[\)\]]/gi, "")
    .replace(/\s*-\s*(?:\d{4}\s+)?(?:remaster\w*|live|deluxe|mono|single|version|ver\.|from\s+).*$/gi, "")
    .trim();
}

function isCoverOrInstrumental(candTitle, targetTitle) {
  const badWords = /(?:cover|翻唱|伴奏|纯音乐|piano|钢琴|instrumental|karaoke)/i;
  return badWords.test(candTitle) && !badWords.test(targetTitle);
}

function scoreLyricCandidate(c, target) {
  const diffSec = Math.abs(c.durationSec - target.durationSec);
  if (diffSec > 3) return null;
  if (isCoverOrInstrumental(c.title, target.name)) return null;

  const normT = normLyricText(target.name);
  const normCleanT = normLyricText(stripTitleNoise(target.name));
  const normC = normLyricText(c.title);
  const normCleanC = normLyricText(stripTitleNoise(c.title));

  let titleScore = 0;
  if (normC && normC === normT) {
    titleScore = 60;
  } else if (normCleanC && normCleanT && normCleanC === normCleanT) {
    titleScore = 55;
  } else if (normCleanC && normCleanT && (normCleanC.includes(normCleanT) || normCleanT.includes(normCleanC))) {
    titleScore = 35;
  }
  if (titleScore === 0) return null;

  const targetArtists = target.artists?.length ? target.artists : (target.artist ? [target.artist] : []);
  const normCandAuthor = normLyricText(c.author);
  let artistScore = 0;
  for (const a of targetArtists) {
    const normA = normLyricText(a);
    if (!normA) continue;
    if (normCandAuthor.includes(normA) || normA.includes(normCandAuthor)) {
      artistScore = 40;
      break;
    }
    const cjkChars = normA.match(/[\p{Script=Han}\p{Script=Hiragana}\p{Script=Katakana}]/gu);
    if (cjkChars && cjkChars.length > 0) {
      let matchedCount = 0;
      for (const ch of cjkChars) {
        if (normCandAuthor.includes(ch)) matchedCount++;
      }
      if (matchedCount >= Math.ceil(cjkChars.length / 2)) {
        artistScore = 40;
        break;
      }
    }
  }

  const isAsciiAuthorTarget = /^[a-z0-9\s]+$/i.test(target.artist || "");
  const isAsciiAuthorCand = /^[a-z0-9\s]+$/i.test(c.author || "");
  if (isAsciiAuthorTarget && isAsciiAuthorCand && !artistScore) {
    return null;
  }

  const isCjkTarget = /[\p{Script=Han}\p{Script=Hiragana}\p{Script=Katakana}]/u.test(target.artist || "");
  const isCjkCand = /[\p{Script=Han}\p{Script=Hiragana}\p{Script=Katakana}]/u.test(c.author || "");
  if (isCjkTarget && isCjkCand && !artistScore) {
    return null;
  }

  const durScore = (3 - diffSec) * 5;
  const syncScore = c.hasSync ? 20 : 0;
  return { score: titleScore + artistScore + durScore + syncScore, diffSec };
}

// Lyrics with no times, spread evenly over the song. Given as they are, every
// line would start at 0 and the app would scroll straight to the last one.
function spreadPlainLyrics(text, durationMs) {
  const texts = text.split(/\r?\n/).map((l) => l.trim());
  while (texts.length && !texts[texts.length - 1]) texts.pop();
  if (!texts.length) return { lrc: "" };
  const step = durationMs ? durationMs / texts.length : 4000;
  return { lines: texts.map((line, i) => ({ start: Math.round(i * step), text: line })) };
}

const hasLrcTimes = (lrc) => /^\s*\[\d+:\d+/m.test(lrc);

export async function lyrics({ id }) {
  // The first lyrics without times that are found, if none of the sources has
  // timed ones.
  let plain = "";

  // 1. Try Spotify color-lyrics (if available)
  try {
    const token = await getToken();
    const clientId = tokenInfo?.clientId || "d8a5ed958d274c2e8ee717e6a4b0971d";
    const clientToken = await getClientToken(clientId).catch(() => "");
    const headers = {
      Authorization: `Bearer ${token}`,
      "User-Agent": webUA,
      "App-Platform": "WebPlayer",
      Accept: "application/json",
    };
    if (clientToken) {
      headers["client-token"] = clientToken;
    }
    const res = await fetch(
      `https://spclient.wg.spotify.com/color-lyrics/v2/track/${id}?format=json&vType=web-player&market=from_token`,
      { headers }
    );
    if (res.ok) {
      const data = await res.json();
      const lines = data.lyrics?.lines;
      if (Array.isArray(lines) && lines.length && data.lyrics.syncType === "UNSYNCED") {
        plain = lines.map((l) => l.words || "").join("\n");
      } else if (Array.isArray(lines) && lines.length) {
        return {
          lines: lines.map((l) => ({
            start: Number(l.startTimeMs) || 0,
            text: l.words || "",
          })),
        };
      }
    }
  } catch (e) {
    // ignore and fallback
  }

  // Retrieve track metadata for fallback sources
  let trackName = "";
  let artistName = "";
  let artists = [];
  let durationSec = 0;
  let durationMs = 0;
  try {
    const tRes = await gql("getTrack", "612585ae06ba435ad26369870deaae23b5c8800a256cd8a57e08eddc25a37294", {
      uri: `spotify:track:${id}`,
    });
    const tData = tRes?.data?.trackUnion;
    if (tData) {
      trackName = tData.name || "";
      artistName = tData.firstArtist?.items?.[0]?.profile?.name || "";
      artists = [
        ...(tData.firstArtist?.items || []),
        ...(tData.otherArtists?.items || []),
      ]
        .map((a) => a?.profile?.name)
        .filter(Boolean);
      durationMs = tData.duration?.totalMilliseconds || 0;
      durationSec = Math.round(durationMs / 1000);
    }
  } catch (e) {
    console.warn("lyrics metadata error:", e.message);
  }

  if (!trackName) {
    return plain ? spreadPlainLyrics(plain, durationMs) : { lrc: "" };
  }

  const target = { name: trackName, artist: artistName, artists, durationSec };

  // 2. Fallback to LRCLIB /api/get (exact match)
  try {
    const lrcUrl = `https://lrclib.net/api/get?track_name=${encodeURIComponent(trackName)}&artist_name=${encodeURIComponent(artistName)}&duration=${durationSec}`;
    const lrcRes = await fetch(lrcUrl, {
      headers: { "User-Agent": "MyGoMusic-Spotify/0.1.0" },
    });
    if (lrcRes.ok) {
      const lrcData = await lrcRes.json();
      if (lrcData.syncedLyrics?.trim()) {
        return { lrc: lrcData.syncedLyrics };
      }
      plain ||= lrcData.plainLyrics?.trim() || "";
    }
  } catch (e) {
    console.warn("lrclib get error:", e.message);
  }

  // 3. Fallback to LRCLIB /api/search
  try {
    const query = `${trackName} ${artistName}`.trim();
    const urlsToTry = [
      `https://lrclib.net/api/search?q=${encodeURIComponent(query)}`,
    ];
    if (trackName && trackName !== query) {
      urlsToTry.push(`https://lrclib.net/api/search?q=${encodeURIComponent(trackName)}`);
    }
    for (const lrcSearchUrl of urlsToTry) {
      const lrcSearchRes = await fetch(lrcSearchUrl, {
        headers: { "User-Agent": "MyGoMusic-Spotify/0.1.0" },
      });
      if (lrcSearchRes.ok) {
        const items = await lrcSearchRes.json();
        if (Array.isArray(items) && items.length) {
          const scored = [];
          for (const it of items.slice(0, 10)) {
            const lyric = it.syncedLyrics || it.plainLyrics;
            if (!lyric || !lyric.trim()) continue;
            const cand = {
              title: it.trackName || it.name || "",
              author: it.artistName || "",
              durationSec: Math.round(Number(it.duration) || 0),
              hasSync: Boolean(it.syncedLyrics && it.syncedLyrics.trim()),
              lyric,
            };
            const match = scoreLyricCandidate(cand, target);
            if (match) {
              scored.push({ cand, score: match.score });
            }
          }
          scored.sort((a, b) => b.score - a.score);
          const timed = scored.find((item) => item.cand.hasSync);
          if (timed) {
            return { lrc: timed.cand.lyric };
          }
          plain ||= scored[0]?.cand.lyric.trim() || "";
        }
      }
    }
  } catch (e) {
    console.warn("lrclib search error:", e.message);
  }

  // 4. Fallback to NetEase Cloud Music (网易云音乐)
  try {
    const query = `${trackName} ${artistName}`.trim();
    const urlsToTry = [
      `https://music.163.com/api/cloudsearch/pc?s=${encodeURIComponent(query)}&type=1&limit=10`,
    ];
    if (trackName && trackName !== query) {
      urlsToTry.push(`https://music.163.com/api/cloudsearch/pc?s=${encodeURIComponent(trackName)}&type=1&limit=10`);
    }
    for (const neSearchUrl of urlsToTry) {
      const neRes = await fetch(neSearchUrl, {
        headers: { "User-Agent": webUA },
      });
      if (neRes.ok) {
        const neData = await neRes.json();
        const songs = neData?.result?.songs || [];
        const scored = [];
        for (const s of songs.slice(0, 10)) {
          const cand = {
            id: s.id,
            title: s.name || "",
            author: (s.ar || []).map((a) => a?.name).filter(Boolean).join(" / "),
            durationSec: Math.round((s.dt || 0) / 1000),
            hasSync: true,
          };
          const match = scoreLyricCandidate(cand, target);
          if (match) {
            scored.push({ cand, score: match.score });
          }
        }
        scored.sort((a, b) => b.score - a.score);
        for (const item of scored) {
          const lyricUrl = `https://music.163.com/api/song/lyric?id=${item.cand.id}&lv=1&tv=-1`;
          const lyrRes = await fetch(lyricUrl, {
            headers: { "User-Agent": webUA },
          });
          if (lyrRes.ok) {
            const lyrData = await lyrRes.json();
            const lrc = lyrData?.lrc?.lyric;
            if (lrc && typeof lrc === "string") {
              const clean = lrc.trim();
              if (clean && !clean.includes("纯音乐，请欣赏")) {
                if (hasLrcTimes(clean)) return { lrc: clean };
                plain ||= clean;
              }
            }
          }
        }
        if (scored.length > 0) {
          break;
        }
      }
    }
  } catch (e) {
    console.warn("netease lyrics error:", e.message);
  }

  return plain ? spreadPlainLyrics(plain, durationMs) : { lrc: "" };
}

// ============================================================================
// YouTube Audio Engine (Adapted from egoist/mygo-music-youtube-music)
// ============================================================================

const ytSite = "https://music.youtube.com";

function clientVersion() {
  const d = new Date().toISOString().slice(0, 10).replaceAll("-", "");
  return `1.${d}.01.00`;
}

const remix = {
  get client() {
    return { clientName: "WEB_REMIX", clientVersion: clientVersion(), hl: host.language() === "zh-CN" ? "zh-CN" : "en" };
  },
};

const visionOS = (visitor) => ({
  client: {
    clientName: "VISIONOS",
    clientVersion: "1.02",
    deviceMake: "Apple",
    deviceModel: "RealityDevice17,1",
    userAgent: visionUA,
    osName: "visionOS",
    osVersion: "26.5.23O471",
    visitorData: visitor,
  },
  headers: {
    "user-agent": visionUA,
    "x-goog-visitor-id": visitor,
    "x-youtube-client-name": "101",
    "x-youtube-client-version": "1.02",
  },
  anonymous: true,
});

async function ytCall(endpoint, body, as = remix) {
  const res = await fetch(`${ytSite}/youtubei/v1/${endpoint}?prettyPrint=false`, {
    method: "POST",
    headers: {
      "content-type": "application/json",
      "user-agent": webUA,
      origin: ytSite,
      "x-origin": ytSite,
      ...as.headers,
    },
    body: JSON.stringify({ context: { client: as.client }, ...body }),
  });
  if (!res.ok) throw new Error(`YouTube ${endpoint}: ${res.status}`);
  return res.json();
}

function findAll(node, name, out = []) {
  if (Array.isArray(node)) {
    for (const item of node) findAll(item, name, out);
  } else if (node && typeof node === "object") {
    for (const key of Object.keys(node)) {
      if (key === name) out.push(node[key]);
      else findAll(node[key], name, out);
    }
  }
  return out;
}

const findOne = (node, name) => findAll(node, name)[0];

const textOf = (nd) => (nd ? nd.simpleText || (nd.runs || []).map((r) => r.text).join("") : "");

function msOf(text) {
  if (!text || !/^\d+(:\d+)+$/.test(text)) return 0;
  return text.split(":").reduce((sum, n) => sum * 60 + Number(n), 0) * 1000;
}

async function searchSongs(query) {
  // This is YouTube Music's Songs filter. Its structured rows come from the
  // music catalog and expose artist/album metadata even when Spotify and YT
  // display different scripts for the same artist.
  const filter = "EgWKAQIIAWoMEA4QChADEAQQCRAF";
  const res = await ytCall("search", { query, params: decodeURIComponent(filter) });
  const shelf = findOne(res, "musicShelfRenderer");
  const items = shelf?.contents || [];
  const tracks = [];
  for (let rank = 0; rank < items.length; rank += 1) {
    const item = items[rank];
    const r = item.musicResponsiveListItemRenderer;
    if (!r) continue;
    const columns = (r.flexColumns || []).map((c) => c.musicResponsiveListItemFlexColumnRenderer?.text);
    const title = textOf(columns[0]);
    const nav = columns[0]?.runs?.[0]?.navigationEndpoint;
    const videoId = r.playlistItemData?.videoId || nav?.watchEndpoint?.videoId;
    const fixed = (r.fixedColumns || []).map((c) => textOf(c.musicResponsiveListItemFixedColumnRenderer?.text));
    const runs = columns.slice(1).flatMap((c) => [...(c?.runs || []), { text: "•" }]);
    let durationMs = msOf(fixed[0]);
    if (!durationMs) {
      for (const run of runs) {
        const d = msOf(run.text);
        if (d) {
          durationMs = d;
          break;
        }
      }
    }
    const author = columns[1]?.runs?.[0]?.text || textOf(columns[1]);
    const fullSubtitle = textOf(columns[1]);
    const metadata = columns.slice(1).flatMap((column) => column?.runs?.map((run) => run.text) || []).join(" ");
    const viewCount = parseViewCount(metadata);
    const badges = JSON.stringify(r.badges || []);
    const officialBadge = /OFFICIAL_ARTIST_BADGE|Official Artist Channel/i.test(badges);
    if (videoId) {
      tracks.push({ videoId, title, author, durationMs, viewCount, officialBadge, rank,
        topicOfficial: /\bTopic\b/i.test(fullSubtitle), catalogResult: true });
    }
  }
  return tracks;
}

async function webCall(endpoint, body) {
  const date = new Date().toISOString().slice(0, 10).replaceAll("-", "");
  const res = await fetch(`https://www.youtube.com/youtubei/v1/${endpoint}?prettyPrint=false`, {
    method: "POST",
    headers: {
      "content-type": "application/json",
      "user-agent": webUA,
      origin: "https://www.youtube.com",
      "x-origin": "https://www.youtube.com",
    },
    body: JSON.stringify({
      context: { client: { clientName: "WEB", clientVersion: `2.${date}.00.00`, hl: host.language() === "zh-CN" ? "zh-CN" : "en", gl: "JP" } },
      ...body,
    }),
  });
  if (!res.ok) throw new Error(`YouTube ${endpoint}: ${res.status}`);
  return res.json();
}

async function searchYouTubeVideos(query) {
  const data = await webCall("search", { query });
  return findAll(data, "videoRenderer").map((video, rank) => ({
    videoId: video.videoId,
    rank,
    title: textOf(video.title),
    author: textOf(video.ownerText || video.longBylineText),
    durationMs: msOf(textOf(video.lengthText)),
    viewCount: parseViewCount(textOf(video.viewCountText)),
    officialBadge: /OFFICIAL_ARTIST_BADGE|Official Artist Channel/i.test(JSON.stringify(video.ownerBadges || [])),
    source: "youtube",
    topicOfficial: /\bTopic\b/i.test(textOf(video.ownerText || video.longBylineText)),
  })).filter((candidate) => candidate.videoId && candidate.title);
}

function parseViewCount(text) {
  const match = (text || "").match(/([\d,.]+)\s*(K|M|B|千|万|億)\s*(?:views?|回視聴|次观看|次播放)?|([\d,]+)\s*(?:views?|回視聴|次观看|次播放)/i);
  if (!match) return 0;
  const value = Number((match[1] || match[3]).replace(/,/g, ""));
  const multiplier = { k: 1e3, m: 1e6, b: 1e9, "千": 1e3, "万": 1e4, "億": 1e8 }[(match[2] || "").toLowerCase()] || 1;
  return Number.isFinite(value) ? value * multiplier : 0;
}

function normalizeMatchText(value) {
  return (value || "")
    .normalize("NFKC")
    .toLocaleLowerCase()
    .replace(/[^\p{L}\p{N}]/gu, "");
}

function normalizeMatchTitle(value, ...artistNames) {
  let title = (value || "").normalize("NFKC").trim();
  // Official uploads commonly prefix the artist, or append video/lyrics labels.
  for (const artist of artistNames.filter(Boolean)) {
    const escaped = artist.normalize("NFKC").trim().replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    if (escaped) title = title.replace(new RegExp(`^${escaped}\\s*[-–—:：|｜]\\s*`, "i"), "");
  }
  title = title
    .replace(/\s*[[(（【].*?(?:official|music video|mv|lyrics?|audio|visualizer|lyric video).*?[)\]）】]\s*/giu, " ")
    .replace(/\b(?:official|music video|lyric video|lyrics?|audio|visualizer|高清|官方版)\b/giu, " ");
  return normalizeMatchText(title);
}

function versionMarker(value) {
  const text = (value || "").normalize("NFKC").toLocaleLowerCase();
  const markers = [
    ["piano", /\bpiano\b|ピアノ/u],
    ["acoustic", /\bacoustic\b|アコースティック/u],
    ["live", /\blive\b|ライブ/u],
    ["cover", /\bcover\b|カバー/u],
    ["karaoke", /\bkaraoke\b|カラオケ/u],
    ["instrumental", /\binstrumental\b|インスト/u],
    ["remix", /\bremix\b|リミックス/u],
    ["sped-up", /\bsped[ -]?up\b/u],
    ["slowed", /\bslowed\b/u],
    ["nightcore", /\bnightcore\b/u],
    ["first-take", /\bthe first take\b|\bfirst take\b/u],
    ["live", /現場|现场|演唱會|演唱会|巡迴|巡回|live映像/u],
    ["medley", /medley|串燒|串烧|組曲|组曲/u],
    ["cover", /翻唱|翻奏|カバー/u],
  ];
  return markers.find(([, pattern]) => pattern.test(text))?.[0] || "";
}

function scoreCandidate(c, target) {
  const normTargetTitle = normalizeMatchTitle(target.name, ...target.artists);
  const normCandTitle = normalizeMatchTitle(c.title, ...target.artists, c.author);
  const titleExact = Boolean(normTargetTitle && normCandTitle && normCandTitle === normTargetTitle);
  const titleContains = Boolean(normTargetTitle && normCandTitle && normCandTitle.includes(normTargetTitle));
  const targetArtistNames = target.artists.map(normalizeMatchText).filter(Boolean);
  const channel = normalizeMatchText(c.author);
  const artistMatch = targetArtistNames.some((name) => channel.includes(name));
  const officialTopic = c.topicOfficial === true || /\s-\sTopic$/i.test((c.author || "").trim());
  const officialSource = c.officialBadge === true || officialTopic || c.catalogResult === true;
  const targetVersion = versionMarker(target.name);
  const candidateVersion = versionMarker(c.title);
  const versionMismatch = Boolean(candidateVersion && candidateVersion !== targetVersion);
  const hasDuration = c.durationMs > 0 && target.durationMs > 0;
  const diffSec = hasDuration ? Math.abs(c.durationMs - target.durationMs) / 1000 : 999;
  const durationTolerance = target.durationMs > 0
    ? Math.min(60, Math.max(20, target.durationMs / 1000 * 0.12))
    : 0;
  const durationClose = hasDuration && diffSec <= durationTolerance;
  const durationUnknown = !hasDuration;
  const titleLongEnoughForContains = normTargetTitle.length >= 5;
  const bestArtistTitleRank = c.artistTitleSearchRank ?? 999;

  // Search relevance helps choose between already plausible results. It is not
  // proof that two different titles are language variants of the same song.
  // Official sources keep a head start; uploads without an official claim
  // start from zero and only count as a fallback (see matchSpotifyTrack).
  let score = c.officialBadge ? 220 : (officialTopic ? 190 : (c.catalogResult ? 140 : 0));
  if (artistMatch) score += 35;
  if (titleExact) score += 150;
  else if (titleContains) score += 50;
  if (durationClose) score += Math.max(0, 35 - diffSec * 0.5);
  if (bestArtistTitleRank < 999) score += Math.max(0, 24 - bestArtistTitleRank * 3);
  if (c.viewCount > 0) score += Math.min(8, Math.log10(c.viewCount + 1));
  if (versionMismatch) score -= 1000;

  const exactMatch = titleExact && (durationClose || durationUnknown);
  const safeContainsMatch = titleContains && titleLongEnoughForContains && durationClose &&
    (artistMatch || bestArtistTitleRank <= 2);
  // Many niche or independent artists have no official channel, Topic or
  // catalog entry. Accept such an upload only when everything lines up: the
  // exact title, a known close duration and the right artist (by channel or
  // as a top hit for the artist + title query).
  const artistEvidence = artistMatch || bestArtistTitleRank <= 2;
  const fallbackMatch = titleExact && durationClose && artistEvidence;
  const eligible = !versionMismatch && (officialSource ? (exactMatch || safeContainsMatch) : fallbackMatch);
  // Good enough to stop searching: an official upload with the exact title,
  // matching duration and the right artist.
  const confident = eligible && officialSource && titleExact && durationClose &&
    (artistMatch || bestArtistTitleRank === 0);
  // Which kind of match this is, best first: official with the right artist,
  // then a third-party fallback (which always has the right artist), then an
  // official upload with nothing tying it to the artist, which is often just
  // another artist's song of the same name.
  const tier = !officialSource ? 1 : (artistEvidence ? 0 : 2);
  return { score, diffSec, titleExact, artistMatch, officialSource, versionMismatch, eligible, confident, tier };
}

// ============================================================================
// Curated YouTube sources
// ============================================================================

// Names that are the same artist, in whatever script Spotify or YouTube uses.
const artistAliases = [["陈一发儿", "陳一發兒"]];

function withAliases(artists) {
  const out = [...artists];
  for (const group of artistAliases) {
    if (artists.some((name) => group.includes(name.normalize("NFKC").trim()))) out.push(...group);
  }
  return [...new Set(out)];
}

// Some artists' songs are mostly kept by fans rather than on official
// channels, where general search ranks them poorly. For these artists the
// fans' channels are searched and their playlists looked through first.
const curatedSources = [
  {
    artists: ["陈一发儿", "陳一發兒"],
    // youtube.com/@最愛陈一发儿, thousands of videos: searched, not listed.
    channels: ["UC5ibEE0btMSv_D9A6ZllY4A"],
    playlists: ["PLi3zrmUZHiY-B90BAgSCE9TiYsM7PYbZc"],
  },
];

// One Chinese character for another (OpenCC's TSCharacters and STCharacters,
// first choice), so a title in either script matches a name in the other.
const tsFrom = "丟並乾亂亙亞佇佈佔併來侖侶侷俁係俔俠俥俬倀倆倈倉個們倖倫偉側偵偽傑傖傘備傢傭傯傳傴債傷傾僂僅僉僑僕僞僥僨僱價儀儁儂億儈儉儎儐儔儕儘償優儲儷儺儻儼兇兌兒兗內兩冊冑冪凈凍凜凱別刪剄則剋剎剗剛剝剮剴創剷劃劇劉劊劌劍劑勁動務勛勝勞勢勩勱勳勵勸勻匭匯匱區協卹卻卽厙厠厤厭厲厴參叄叢吒吳吶呂咼員唄唸問啓啞啟啢喚喪喫喬單喲嗆嗇嗊嗎嗚嗩嗶嘆嘍嘓嘔嘖嘗嘜嘩嘮嘯嘰嘵嘸嘽噁噓噝噠噥噦噯噲噴噸噹嚀嚇嚌嚐嚕嚙嚥嚦嚨嚮嚲嚳嚴嚶囀囁囂囅囈囉囌囑囪圇國圍園圓圖團垻埡埰執堅堊堖堝堯報場塊塋塏塒塗塚塢塤塵塹墊墜墮墰墳墶墻墾壇壋壎壓壘壙壚壜壞壟壠壢壩壪壯壺壼壽夠夢夥夾奐奧奩奪奬奮奼妝姍姦娛婁婦婭媧媯媼媽嫋嫗嫵嫺嫻嫿嬀嬃嬈嬋嬌嬙嬡嬤嬪嬰嬸孃孌孫學孿宮寀寢實寧審寫寬寵寶將專尋對導尷屆屍屓屜屢層屨屬岡峯峴島峽崍崑崗崙崢崬嵐嵗嶁嶄嶇嶔嶗嶠嶢嶧嶨嶮嶸嶺嶼嶽巋巒巔巖巰巹帥師帳帶幀幃幗幘幟幣幫幬幹幾庫廁廂廄廈廎廕廚廝廟廠廡廢廣廩廬廳弒弔弳張強彆彈彌彎彔彙彠彥彫彲彿後徑從徠復徵徹恆恥悅悞悵悶悽惡惱惲惻愛愜愨愴愷愾慄態慍慘慚慟慣慤慪慫慮慳慶慼慾憂憊憐憑憒憖憚憤憫憮憲憶懇應懌懍懞懟懣懨懲懶懷懸懺懼懾戀戇戔戧戩戰戱戲戶拋挩挱挾捨捫捱捲掃掄掗掙掛採揀揚換揮揯損搖搗搵搶摑摜摟摯摳摶摺摻撈撏撐撓撟撣撥撫撲撳撻撾撿擁擄擇擊擋擔據擠擣擬擯擰擱擲擴擷擺擻擼擾攄攆攏攔攖攙攛攜攝攢攣攤攪攬敎敓敗敘敵數斂斃斆斕斬斷於旂旣昇時晉晝暈暉暘暢暫曄曆曇曉曏曖曠曨曬書會朧朮東枴柵柺査桿梔梘條梟梲棄棊棖棗棟棧棲棶椏楊楓楨業極榘榦榪榮榲榿構槍槓槤槧槨槮槳槶槼樁樂樅樑樓標樞樣樧樳樸樹樺樿橈橋機橢橫檁檉檔檜檟檢檣檮檯檳檸檻櫃櫓櫚櫛櫝櫞櫟櫥櫧櫨櫪櫫櫬櫱櫳櫸櫻欄欅權欏欒欖欞欽歎歐歟歡歲歷歸歿殘殞殤殫殭殮殯殲殺殻殼毀毆毿氂氈氌氣氫氬氳氾汎汙決沒沖況泝洩洶浹涇涗涼淒淚淥淨淩淪淵淶淺渙減渢渦測渾湊湞湧湯溈準溝溫溮溳溼滄滅滌滎滙滬滯滲滷滸滻滾滿漁漊漚漢漣漬漲漵漸漿潁潑潔潙潛潤潯潰潷潿澀澆澇澐澗澠澤澦澩澮澱濁濃濕濘濚濛濜濟濤濫濰濱濺濼濾瀂瀅瀆瀉瀋瀏瀕瀘瀝瀟瀠瀦瀧瀨瀰瀲瀾灃灄灑灕灘灝灣灤灧灩災為烏烴無煉煒煙煢煥煩煬熅熒熗熱熲熾燁燈燉燒燙燜營燦燬燭燴燻燼燾爍爐爛爭爲爺爾牀牆牘牽犖犛犢犧狀狹狽猙猶猻獁獃獄獅獎獨獪獫獮獰獲獵獷獸獺獻獼玀現琱琺琿瑋瑒瑣瑤瑩瑪瑲璉璡璣璦璫環璵璸璽璿瓊瓏瓔瓚甌甕產産甦甯畝畢畫異畵當疇疊痙痠痾瘂瘋瘍瘓瘞瘡瘧瘮瘲瘺瘻療癆癇癉癒癘癟癡癢癤癥癧癩癬癭癮癰癱癲發皁皚皰皸皺盃盜盞盡監盤盧盪眞眥眾睏睜睞瞘瞞瞶瞼矇矓矚矯硃硜硤硨硯碕碩碭碸確碼磑磚磠磣磧磯磽礄礆礎礙礦礪礫礬礱祕祿禍禎禕禡禦禪禮禰禱禿秈稅稈稜稟種稱穀穌積穎穠穡穢穩穫穭窩窪窮窯窵窶窺竄竅竇竈竊竪競筆筍筧箇箋箏節範築篋篔篠篤篩篳簀簍簑簞簡簣簫簹簽簾籃籌籙籛籜籟籠籤籩籪籬籮籲粵糉糝糞糧糰糲糴糶糹糾紀紂約紅紆紇紈紉紋納紐紓純紕紖紗紘紙級紛紜紝紡紮細紱紲紳紵紹紺紼紿絀終絃組絆絎結絕絛絝絞絡絢給絨絰統絲絳絶絹綁綃綆綈綉綌綏綑經綜綞綠綢綣綫綬維綯綰綱網綳綴綵綸綹綺綻綽綾綿緄緇緊緋緑緒緓緔緗緘緙線緝緞締緡緣緦編緩緬緯緱緲練緶緹緻緼縈縉縊縋縐縑縕縗縛縝縞縟縣縧縫縭縮縱縲縴縵縶縷縹總績繃繅繆繒織繕繚繞繡繢繩繪繫繭繮繯繰繳繹繼繽繾纇纈纊續纍纏纓纔纖纘纜缽罈罌罎罰罵罷羅羆羈羋羣羥羨義羶習翫翬翹翽耬耮聖聞聯聰聲聳聵聶職聹聽聾肅脅脈脛脣脩脫脹腎腖腡腦腫腳腸膃膕膚膠膩膽膾膿臉臍臏臘臚臟臠臢臥臨臺與興舉舊舘艙艤艦艫艱艷芻苧茲荊莊莖莢莧華菴菸萇萊萬萴萵葉葒葤葦葯葷蒐蒓蒔蒕蒞蒼蓀蓆蓋蓮蓯蓴蓽蔔蔘蔞蔣蔥蔦蔭蕁蕆蕎蕒蕓蕕蕘蕢蕩蕪蕭蕷薀薈薊薌薑薔薘薟薦薩薴薹薺藍藎藝藥藪藴藶藹藺蘀蘄蘆蘇蘊蘋蘚蘞蘢蘭蘺蘿虆處虛虜號虧虯蛺蛻蜆蝕蝟蝦蝨蝸螄螞螢螻螿蟄蟈蟎蟣蟬蟯蟲蟶蟻蠁蠅蠆蠍蠐蠑蠔蠟蠣蠨蠱蠶蠻衆衊術衕衚衛衝袞裊裏補裝裡製複褌褘褲褳褸褻襇襉襏襖襝襠襤襪襬襯襲襴覈見覎規覓視覘覡覥覦親覬覯覲覷覺覽覿觀觴觶觸訁訂訃計訊訌討訐訒訓訕訖託記訛訝訟訣訥訩訪設許訴訶診註証詁詆詎詐詒詔評詖詗詘詛詞詠詡詢詣試詩詫詬詭詮詰話該詳詵詼詿誄誅誆誇誌認誑誒誕誘誚語誠誡誣誤誥誦誨說説誰課誶誹誼誾調諂諄談諉請諍諏諑諒論諗諛諜諝諞諡諢諤諦諧諫諭諮諱諳諶諷諸諺諼諾謀謁謂謄謅謊謎謐謔謖謗謙謚講謝謠謡謨謫謬謭謳謹謾譁證譎譏譖識譙譚譜譟譫譭譯議譴護譸譽譾讀讅變讋讎讒讓讕讖讚讜讞豈豎豐豔豬豶貓貝貞貟負財貢貧貨販貪貫責貯貰貲貳貴貶買貸貺費貼貽貿賀賁賂賃賄賅資賈賊賑賒賓賕賙賚賜賞賠賡賢賣賤賦賧質賫賬賭賴賵賺賻購賽賾贄贅贇贈贊贋贍贏贐贓贔贖贗贛贜赬趕趙趨趲跡踐踰踴蹌蹕蹟蹠蹣蹤蹺躂躉躊躋躍躑躒躓躕躚躡躥躦躪軀車軋軌軍軑軒軔軛軟軤軫軲軸軹軺軻軼軾較輅輇輈載輊輒輓輔輕輛輜輝輞輟輥輦輩輪輬輯輳輸輻輼輾輿轀轂轄轅轆轉轍轎轔轟轡轢轤辦辭辮辯農迴逕這連週進遊運過達違遙遜遞遠遡適遲遷選遺遼邁還邇邊邏邐郟郵鄆鄉鄒鄔鄖鄧鄭鄰鄲鄴鄶鄺酇酈醃醖醜醞醟醣醫醬醱釀釁釃釅釋釐釒釓釔釕釗釘釙針釣釤釦釧釩釵釷釹釺鈀鈁鈃鈄鈅鈈鈉鈍鈎鈐鈑鈒鈔鈕鈞鈡鈣鈥鈦鈧鈮鈰鈳鈴鈷鈸鈹鈺鈽鈾鈿鉀鉅鉆鉈鉉鉋鉍鉑鉕鉗鉚鉛鉞鉢鉤鉦鉬鉭鉳鉶鉸鉺鉻鉿銀銃銅銍銑銓銖銘銚銛銜銠銣銥銦銨銩銪銫銬銱銳銷銹銻銼鋁鋃鋅鋇鋌鋏鋒鋙鋝鋟鋣鋤鋥鋦鋨鋩鋪鋭鋮鋯鋰鋱鋶鋸鋼錁錄錆錇錈錏錐錒錕錘錙錚錛錟錠錡錢錦錨錩錫錮錯録錳錶錸錼鍀鍁鍃鍅鍆鍇鍈鍊鍋鍍鍔鍘鍚鍛鍠鍤鍥鍩鍬鍰鍵鍶鍺鍼鍾鎂鎄鎇鎊鎌鎔鎖鎘鎚鎛鎡鎢鎣鎦鎧鎩鎪鎬鎭鎮鎰鎲鎳鎵鎶鎸鎿鏃鏇鏈鏌鏍鏐鏑鏗鏘鏜鏝鏞鏟鏡鏢鏤鏨鏰鏵鏷鏹鏽鐃鐋鐐鐒鐓鐔鐘鐙鐝鐠鐦鐧鐨鐫鐮鐲鐳鐵鐶鐸鐺鐿鑄鑊鑌鑑鑒鑔鑕鑞鑠鑣鑥鑭鑰鑱鑲鑷鑹鑼鑽鑾鑿钁钂長門閂閃閆閈閉開閌閎閏閑閒間閔閘閡閣閤閥閨閩閫閬閭閱閲閶閹閻閼閽閾閿闃闆闇闈闊闋闌闍闐闒闓闔闕闖關闞闠闡闢闤闥陘陝陞陣陰陳陸陽隉隊階隕際隨險隯隱隴隸隻雋雖雙雛雜雞離難雲電霑霢霧霽靂靄靆靈靉靚靜靝靦靨鞏鞝鞦鞽韁韃韆韉韋韌韍韓韙韜韝韞韻響頁頂頃項順頇須頊頌頎頏預頑頒頓頗領頜頡頤頦頭頮頰頲頴頷頸頹頻頽顆題額顎顏顒顓顔願顙顛類顢顥顧顫顬顯顰顱顳顴風颭颮颯颱颳颶颸颺颻颼飀飄飆飈飛飠飢飣飥飩飪飫飭飯飱飲飴飼飽飾飿餃餄餅餈餉養餌餎餏餑餒餓餕餖餘餚餛餜餞餡館餬餱餳餵餶餷餺餼餾餿饁饃饅饈饉饊饋饌饑饒饗饜饞饢馬馭馮馱馳馴馹駁駐駑駒駔駕駘駙駛駝駟駡駢駭駰駱駸駿騁騂騅騌騍騎騏騖騙騤騫騭騮騰騶騷騸騾驀驁驂驃驄驅驊驌驍驏驕驗驚驛驟驢驤驥驦驪驫骯髏髒體髕髖髮鬆鬍鬚鬢鬥鬧鬨鬩鬮鬱鬹魎魘魚魛魢魨魯魴魷魺鮁鮃鮊鮋鮍鮎鮐鮑鮒鮓鮚鮜鮝鮞鮦鮪鮫鮭鮮鮳鮶鮺鯀鯁鯇鯉鯊鯒鯔鯕鯖鯗鯛鯝鯡鯢鯤鯧鯨鯪鯫鯰鯴鯷鯽鯿鰁鰂鰃鰈鰉鰍鰏鰐鰒鰓鰛鰜鰟鰠鰣鰥鰨鰩鰭鰮鰱鰲鰳鰵鰷鰹鰺鰻鰼鰾鱂鱅鱈鱉鱒鱔鱖鱗鱘鱝鱟鱠鱣鱤鱧鱨鱭鱯鱷鱸鱺鳥鳧鳩鳬鳲鳳鳴鳶鴆鴇鴉鴒鴕鴛鴝鴞鴟鴣鴦鴨鴯鴰鴴鴻鴿鵂鵃鵐鵑鵒鵓鵜鵝鵠鵡鵪鵬鵮鵯鵰鵲鵷鵾鶇鶉鶊鶓鶖鶘鶚鶡鶥鶩鶬鶯鶲鶴鶹鶺鶻鶼鶿鷀鷁鷂鷄鷊鷓鷖鷗鷙鷚鷥鷦鷫鷯鷲鷳鷴鷸鷹鷺鷽鸇鸌鸏鸕鸘鸚鸛鸝鸞鹵鹹鹺鹼鹽麗麥麩麪麫麯麴麵麼麽黃黌點黨黲黴黶黷黽黿鼂鼉鼕鼴齊齋齎齏齒齔齕齗齙齜齟齠齡齣齦齧齪齬齲齶齷龍龎龐龔龕龜鿓";
const tsTo = "丢并干乱亘亚伫布占并来仑侣局俣系伣侠伡私伥俩俫仓个们幸伦伟侧侦伪杰伧伞备家佣偬传伛债伤倾偻仅佥侨仆伪侥偾雇价仪俊侬亿侩俭傤傧俦侪尽偿优储俪傩傥俨凶兑儿兖内两册胄幂净冻凛凯别删刭则克刹刬刚剥剐剀创铲划剧刘刽刿剑剂劲动务勋胜劳势勚劢勋励劝匀匦汇匮区协恤却即厍厕历厌厉厣参叁丛咤吴呐吕呙员呗念问启哑启唡唤丧吃乔单哟呛啬唝吗呜唢哔叹喽啯呕啧尝唛哗唠啸叽哓呒啴恶嘘咝哒哝哕嗳哙喷吨当咛吓哜尝噜啮咽呖咙向亸喾严嘤啭嗫嚣冁呓啰苏嘱囱囵国围园圆图团坝垭采执坚垩垴埚尧报场块茔垲埘涂冢坞埙尘堑垫坠堕坛坟垯墙垦坛垱埙压垒圹垆坛坏垄垅坜坝塆壮壶壸寿够梦伙夹奂奥奁夺奖奋姹妆姗奸娱娄妇娅娲妫媪妈袅妪妩娴娴婳妫媭娆婵娇嫱嫒嬷嫔婴婶娘娈孙学孪宫采寝实宁审写宽宠宝将专寻对导尴届尸屃屉屡层屦属冈峰岘岛峡崃昆岗仑峥岽岚岁嵝崭岖嵚崂峤峣峄峃崄嵘岭屿岳岿峦巅岩巯卺帅师帐带帧帏帼帻帜币帮帱干几库厕厢厩厦庼荫厨厮庙厂庑废广廪庐厅弑吊弪张强别弹弥弯录汇彟彦雕彨佛后径从徕复征彻恒耻悦悮怅闷凄恶恼恽恻爱惬悫怆恺忾栗态愠惨惭恸惯悫怄怂虑悭庆戚欲忧惫怜凭愦慭惮愤悯怃宪忆恳应怿懔蒙怼懑恹惩懒怀悬忏惧慑恋戆戋戗戬战戯戏户抛捝挲挟舍扪挨卷扫抡挜挣挂采拣扬换挥搄损摇捣揾抢掴掼搂挚抠抟折掺捞挦撑挠挢掸拨抚扑揿挞挝捡拥掳择击挡担据挤捣拟摈拧搁掷扩撷摆擞撸扰摅撵拢拦撄搀撺携摄攒挛摊搅揽教敚败叙敌数敛毙敩斓斩断于旗既升时晋昼晕晖旸畅暂晔历昙晓向暧旷昽晒书会胧术东拐栅拐查杆栀枧条枭棁弃棋枨枣栋栈栖梾桠杨枫桢业极矩干杩荣榅桤构枪杠梿椠椁椮桨椢椝桩乐枞梁楼标枢样榝桪朴树桦椫桡桥机椭横檩柽档桧槚检樯梼台槟柠槛柜橹榈栉椟橼栎橱槠栌枥橥榇蘖栊榉樱栏榉权椤栾榄棂钦叹欧欤欢岁历归殁残殒殇殚僵殓殡歼杀壳壳毁殴毵牦毡氇气氢氩氲泛泛污决没冲况溯泄汹浃泾涚凉凄泪渌净凌沦渊涞浅涣减沨涡测浑凑浈涌汤沩准沟温浉涢湿沧灭涤荥汇沪滞渗卤浒浐滚满渔溇沤汉涟渍涨溆渐浆颍泼洁沩潜润浔溃滗涠涩浇涝沄涧渑泽滪泶浍淀浊浓湿泞溁蒙浕济涛滥潍滨溅泺滤澛滢渎泻沈浏濒泸沥潇潆潴泷濑弥潋澜沣滠洒漓滩灏湾滦滟滟灾为乌烃无炼炜烟茕焕烦炀煴荧炝热颎炽烨灯炖烧烫焖营灿毁烛烩熏烬焘烁炉烂争为爷尔床墙牍牵荦牦犊牺状狭狈狰犹狲犸呆狱狮奖独狯猃狝狞获猎犷兽獭献猕猡现雕珐珲玮玚琐瑶莹玛玱琏琎玑瑷珰环玙瑸玺璇琼珑璎瓒瓯瓮产产苏宁亩毕画异画当畴叠痉酸疴痖疯疡痪瘗疮疟瘆疭瘘瘘疗痨痫瘅愈疠瘪痴痒疖症疬癞癣瘿瘾痈瘫癫发皂皑疱皲皱杯盗盏尽监盘卢荡真眦众困睁睐眍瞒瞆睑蒙眬瞩矫朱硁硖砗砚埼硕砀砜确码硙砖硵碜碛矶硗硚硷础碍矿砺砾矾砻秘禄祸祯祎祃御禅礼祢祷秃籼税秆棱禀种称谷稣积颖秾穑秽稳获穞窝洼穷窑窎窭窥窜窍窦灶窃竖竞笔笋笕个笺筝节范筑箧筼筿笃筛筚箦篓蓑箪简篑箫筜签帘篮筹箓篯箨籁笼签笾簖篱箩吁粤粽糁粪粮团粝籴粜纟纠纪纣约红纡纥纨纫纹纳纽纾纯纰纼纱纮纸级纷纭纴纺扎细绂绁绅纻绍绀绋绐绌终弦组绊绗结绝绦绔绞络绚给绒绖统丝绛绝绢绑绡绠绨绣绤绥捆经综缍绿绸绻线绶维绹绾纲网绷缀彩纶绺绮绽绰绫绵绲缁紧绯绿绪绬绱缃缄缂线缉缎缔缗缘缌编缓缅纬缑缈练缏缇致缊萦缙缢缒绉缣缊缞缚缜缟缛县绦缝缡缩纵缧纤缦絷缕缥总绩绷缫缪缯织缮缭绕绣缋绳绘系茧缰缳缲缴绎继缤缱颣缬纩续累缠缨才纤缵缆钵坛罂坛罚骂罢罗罴羁芈群羟羡义膻习玩翚翘翙耧耢圣闻联聪声耸聩聂职聍听聋肃胁脉胫唇修脱胀肾胨脶脑肿脚肠腽腘肤胶腻胆脍脓脸脐膑腊胪脏脔臜卧临台与兴举旧馆舱舣舰舻艰艳刍苎兹荆庄茎荚苋华庵烟苌莱万荝莴叶荭荮苇药荤搜莼莳蒀莅苍荪席盖莲苁莼荜卜参蒌蒋葱茑荫荨蒇荞荬芸莸荛蒉荡芜萧蓣蕰荟蓟芗姜蔷荙莶荐萨苧苔荠蓝荩艺药薮蕴苈蔼蔺萚蕲芦苏蕴苹藓蔹茏兰蓠萝蔂处虚虏号亏虬蛱蜕蚬蚀猬虾虱蜗蛳蚂萤蝼螀蛰蝈螨虮蝉蛲虫蛏蚁蚃蝇虿蝎蛴蝾蚝蜡蛎蟏蛊蚕蛮众蔑术同胡卫冲衮袅里补装里制复裈袆裤裢褛亵裥裥袯袄裣裆褴袜摆衬袭襕核见觃规觅视觇觋觍觎亲觊觏觐觑觉览觌观觞觯触讠订讣计讯讧讨讦讱训讪讫托记讹讶讼诀讷讻访设许诉诃诊注证诂诋讵诈诒诏评诐诇诎诅词咏诩询诣试诗诧诟诡诠诘话该详诜诙诖诔诛诓夸志认诳诶诞诱诮语诚诫诬误诰诵诲说说谁课谇诽谊訚调谄谆谈诿请诤诹诼谅论谂谀谍谞谝谥诨谔谛谐谏谕咨讳谙谌讽诸谚谖诺谋谒谓誊诌谎谜谧谑谡谤谦谥讲谢谣谣谟谪谬谫讴谨谩哗证谲讥谮识谯谭谱噪谵毁译议谴护诪誉谫读谉变詟雠谗让谰谶赞谠谳岂竖丰艳猪豮猫贝贞贠负财贡贫货贩贪贯责贮贳赀贰贵贬买贷贶费贴贻贸贺贲赂赁贿赅资贾贼赈赊宾赇赒赉赐赏赔赓贤卖贱赋赕质赍账赌赖赗赚赙购赛赜贽赘赟赠赞赝赡赢赆赃赑赎赝赣赃赪赶赵趋趱迹践逾踊跄跸迹跖蹒踪跷跶趸踌跻跃踯跞踬蹰跹蹑蹿躜躏躯车轧轨军轪轩轫轭软轷轸轱轴轵轺轲轶轼较辂辁辀载轾辄挽辅轻辆辎辉辋辍辊辇辈轮辌辑辏输辐辒辗舆辒毂辖辕辘转辙轿辚轰辔轹轳办辞辫辩农回迳这连周进游运过达违遥逊递远溯适迟迁选遗辽迈还迩边逻逦郏邮郓乡邹邬郧邓郑邻郸邺郐邝酂郦腌酝丑酝蒏糖医酱酦酿衅酾酽释厘钅钆钇钌钊钉钋针钓钐扣钏钒钗钍钕钎钯钫钘钭钥钚钠钝钩钤钣钑钞钮钧钟钙钬钛钪铌铈钶铃钴钹铍钰钸铀钿钾巨钻铊铉铇铋铂钷钳铆铅钺钵钩钲钼钽锫铏铰铒铬铪银铳铜铚铣铨铢铭铫铦衔铑铷铱铟铵铥铕铯铐铞锐销锈锑锉铝锒锌钡铤铗锋铻锊锓铘锄锃锔锇铓铺锐铖锆锂铽锍锯钢锞录锖锫锩铔锥锕锟锤锱铮锛锬锭锜钱锦锚锠锡锢错录锰表铼镎锝锨锪钫钔锴锳炼锅镀锷铡钖锻锽锸锲锘锹锾键锶锗针钟镁锿镅镑镰镕锁镉锤镈镃钨蓥镏铠铩锼镐镇镇镒镋镍镓鿔镌镎镞旋链镆镙镠镝铿锵镗镘镛铲镜镖镂錾镚铧镤镪锈铙铴镣铹镦镡钟镫镢镨锎锏镄镌镰镯镭铁镮铎铛镱铸镬镔鉴鉴镲锧镴铄镳镥镧钥镵镶镊镩锣钻銮凿镢镋长门闩闪闫闬闭开闶闳闰闲闲间闵闸阂阁合阀闺闽阃阆闾阅阅阊阉阎阏阍阈阌阒板暗闱阔阕阑阇阗阘闿阖阙闯关阚阓阐辟阛闼陉陕升阵阴陈陆阳陧队阶陨际随险陦隐陇隶只隽虽双雏杂鸡离难云电沾霡雾霁雳霭叇灵叆靓静靔腼靥巩绱秋鞒缰鞑千鞯韦韧韨韩韪韬鞲韫韵响页顶顷项顺顸须顼颂颀颃预顽颁顿颇领颌颉颐颏头颒颊颋颕颔颈颓频颓颗题额颚颜颙颛颜愿颡颠类颟颢顾颤颥显颦颅颞颧风飐飑飒台刮飓飔飏飖飕飗飘飙飚飞饣饥饤饦饨饪饫饬饭飧饮饴饲饱饰饳饺饸饼糍饷养饵饹饻饽馁饿馂饾余肴馄馃饯馅馆糊糇饧喂馉馇馎饩馏馊馌馍馒馐馑馓馈馔饥饶飨餍馋馕马驭冯驮驰驯驲驳驻驽驹驵驾骀驸驶驼驷骂骈骇骃骆骎骏骋骍骓骔骒骑骐骛骗骙骞骘骝腾驺骚骟骡蓦骜骖骠骢驱骅骕骁骣骄验惊驿骤驴骧骥骦骊骉肮髅脏体髌髋发松胡须鬓斗闹哄阋阄郁鬶魉魇鱼鱽鱾鲀鲁鲂鱿鲄鲅鲆鲌鲉鲏鲇鲐鲍鲋鲊鲒鲘鲞鲕鲖鲔鲛鲑鲜鲓鲪鲝鲧鲠鲩鲤鲨鲬鲻鲯鲭鲞鲷鲴鲱鲵鲲鲳鲸鲮鲰鲶鲺鳀鲫鳊鳈鲗鳂鲽鳇鳅鲾鳄鳆鳃鳁鳒鳑鳋鲥鳏鳎鳐鳍鳁鲢鳌鳓鳘鲦鲣鲹鳗鳛鳔鳉鳙鳕鳖鳟鳝鳜鳞鲟鲼鲎鲙鳣鳡鳢鲿鲚鳠鳄鲈鲡鸟凫鸠凫鸤凤鸣鸢鸩鸨鸦鸰鸵鸳鸲鸮鸱鸪鸯鸭鸸鸹鸻鸿鸽鸺鸼鹀鹃鹆鹁鹈鹅鹄鹉鹌鹏鹐鹎雕鹊鹓鹍鸫鹑鹒鹋鹙鹕鹗鹖鹛鹜鸧莺鹟鹤鹠鹡鹘鹣鹚鹚鹢鹞鸡鹝鹧鹥鸥鸷鹨鸶鹪鹔鹩鹫鹇鹇鹬鹰鹭鸴鹯鹱鹲鸬鹴鹦鹳鹂鸾卤咸鹾碱盐丽麦麸面面曲曲面么么黄黉点党黪霉黡黩黾鼋鼌鼍冬鼹齐斋赍齑齿龀龁龂龅龇龃龆龄出龈啮龊龉龋腭龌龙厐庞龚龛龟鿒";
const stFrom = "万与丑专业丛东丝丢两严丧个丰临为丽举么义乌乐乔习乡书买乱争于亏云亘亚产亩亲亵亸亿仅仆从仑仓仪们价众优伙会伛伞伟传伡伣伤伥伦伧伪伫体余佣佥侠侣侥侦侧侨侩侪侬侭俣俦俨俩俪俫俭债倾偬偻偾偿傤傥傧储傩儿兑兖党兰关兴兹养兽冁内冈册写军农冯冲决况冻净凄准凉减凑凛几凤凫凭凯凶击凿刍划刘则刚创删别刬刭刹刽刿剀剂剐剑剥剧劝办务劢动励劲劳势勋勚匀匦匮区医华协单卖占卢卤卧卫却卺厂厅历厉压厌厍厐厕厘厢厣厦厨厩厮县叁参叆叇双发变叙叠台叶号叹叽吁吃后吓吕吗吨听启吴呐呒呓呕呖呗员呙呛呜咏咙咛咝咤咨咸响哑哒哓哔哕哗哙哜哝哟唇唛唝唠唡唢唤啧啬啭啮啯啰啴啸喷喽喾嗫嗳嘘嘤嘱噜嚣团园囱围囵国图圆圣圹场坏块坚坛坜坝坞坟坠垄垅垆垒垦垩垫垭垯垱垲垴埘埙埚堑堕塆墙壮声壳壶壸处备复够头夸夹夺奁奂奋奖奥妆妇妈妩妪妫姗姹娄娅娆娇娈娱娲娴婳婴婵婶媪媭嫒嫔嫱嬷孙学孪宁宝实宠审宪宫宽宾寝对寻导寿将尔尘尝尧尴尸尽层屃屉届属屡屦屿岁岂岖岗岘岚岛岩岭岳岽岿峃峄峡峣峤峥峦峰崂崃崄崭嵘嵚嵝巅巩巯币帅师帏帐帘帜带帧帮帱帻帼幂干并广庄庆床庐庑库应庙庞废庼廪开异弃弑张弥弪弯弹强归当录彟彦彨彻征径徕忆忏忧忾怀态怂怃怄怅怆怜总怼怿恋恒恳恶恸恹恺恻恼恽悦悫悬悭悮悯惊惧惨惩惫惬惭惮惯愠愤愦愿慑慭懑懒懔戆戋戏戗战戬戯户扑托执扩扪扫扬扰抚抛抟抠抡抢护报担拟拢拣拥拦拧拨择挂挚挛挜挝挞挟挠挡挢挣挤挥挦捝捞损捡换捣据掳掴掷掸掺掼揽揾揿搀搁搂搄搅携摄摅摆摇摈摊撄撑撵撷撸撺擞攒敌敚敛敩数斋斓斗斩断无旧时旷旸昙昵昼昽显晋晒晓晔晕晖暂暧术朴机杀杂权杠条来杨杩杰极构枞枢枣枥枧枨枪枫枭柜柠柽栀栅标栈栉栊栋栌栎栏树栖栗样栾桠桡桢档桤桥桦桧桨桩桪梦梼梾梿检棁棂椁椝椟椠椢椤椫椭椮楼榄榅榇榈榉榝槚槛槟槠横樯樱橥橱橹橼檩欢欤欧歼殁殇残殒殓殚殡殴毁毂毕毙毡毵氇气氢氩氲汇汉汤汹沄沟没沣沤沥沦沧沨沩沪泞泪泶泷泸泺泻泼泽泾洁洒洼浃浅浆浇浈浉浊测浍济浏浐浑浒浓浔浕涂涌涚涛涝涞涟涠涡涢涣涤润涧涨涩淀渊渌渍渎渐渑渔渖渗温游湾湿溁溃溅溆溇滗滚滞滟滠满滢滤滥滦滨滩滪潆潇潋潍潜潴澛澜濑濒灏灭灯灵灶灾灿炀炉炖炜炝点炼炽烁烂烃烛烟烦烧烨烩烫烬热焕焖焘煴熏爱爷牍牦牵牺犊状犷犸犹狈狝狞独狭狮狯狰狱狲猃猎猕猡猪猫猬献獭玑玙玚玛玮环现玱玺珐珑珰珲琎琏琐琼瑶瑷瑸璎瓒瓮瓯电画畅畴疖疗疟疠疡疬疭疮疯疱疴痈痉痒痖痨痪痫痴瘅瘆瘗瘘瘪瘫瘾瘿癞癣癫皂皑皱皲盏盐监盖盗盘眍眦眬睁睐睑瞆瞒瞩矫矶矾矿砀码砖砗砚砜砺砻砾础硁硕硖硗硙硚确硵硷碍碛碜碱礼祃祎祢祯祷祸禀禄禅离秃秆种秘积称秽秾稆税稣稳穑穞穷窃窍窎窑窜窝窥窦窭竖竞笃笋笔笕笺笼笾筑筚筛筜筝筹筼签筿简箓箦箧箨箩箪箫篑篓篮篯篱簖籁籴类籼粜粝粤粪粮粽糁糇糍紧絷緼縆纟纠纡红纣纤纥约级纨纩纪纫纬纭纮纯纰纱纲纳纴纵纶纷纸纹纺纻纼纽纾线绀绁绂练组绅细织终绉绊绋绌绍绎经绐绑绒结绔绕绖绗绘给绚绛络绝绞统绠绡绢绣绤绥绦继绨绩绪绫绬续绮绯绰绱绲绳维绵绶绷绸绹绺绻综绽绾绿缀缁缂缃缄缅缆缇缈缉缊缋缌缍缎缏缐缑缒缓缔缕编缗缘缙缚缛缜缝缞缟缠缡缢缣缤缥缦缧缨缩缪缫缬缭缮缯缰缱缲缳缴缵罂网罗罚罢罴羁羟羡群翘翙翚耢耧耸耻聂聋职聍联聩聪肃肠肤肮肴肾肿胀胁胆胜胧胨胪胫胶脉脍脏脐脑脓脔脚脱脶脸腊腌腘腭腻腼腽腾膑膻臜舆舣舰舱舻艰艳艺节芈芗芜芦苁苇苈苋苌苍苎苏苧苹范茎茏茑茔茕茧荆荐荙荚荛荜荝荞荟荠荡荣荤荥荦荧荨荩荪荫荬荭荮药莅莱莲莳莴莶获莸莹莺莼萚萝萤营萦萧萨葱蒀蒇蒉蒋蒌蒏蓝蓟蓠蓣蓥蓦蔂蔷蔹蔺蔼蕰蕲蕴薮藓藴蘖虏虑虚虫虬虮虱虽虾虿蚀蚁蚂蚃蚕蚝蚬蛊蛎蛏蛮蛰蛱蛲蛳蛴蜕蜗蜡蝇蝈蝉蝎蝼蝾螀螨蟏衅衔补衬衮袄袅袆袜袭袯装裆裈裢裣裤裥褛褴襕见观觃规觅视觇览觉觊觋觌觍觎觏觐觑觞触觯訚詟誉誊讠计订讣认讥讦讧讨让讪讫讬训议讯记讱讲讳讴讵讶讷许讹论讻讼讽设访诀证诂诃评诅识诇诈诉诊诋诌词诎诏诐译诒诓诔试诖诗诘诙诚诛诜话诞诟诠诡询诣诤该详诧诨诩诪诫诬语诮误诰诱诲诳说诵诶请诸诹诺读诼诽课诿谀谁谂调谄谅谆谇谈谉谊谋谌谍谎谏谐谑谒谓谔谕谖谗谘谙谚谛谜谝谞谟谠谡谢谣谤谥谦谧谨谩谪谫谬谭谮谯谰谱谲谳谴谵谶豮贝贞负贠贡财责贤败账货质贩贪贫贬购贮贯贰贱贲贳贴贵贶贷贸费贺贻贼贽贾贿赀赁赂赃资赅赆赇赈赉赊赋赌赍赎赏赐赑赒赓赔赕赖赗赘赙赚赛赜赝赞赟赠赡赢赣赪赵赶趋趱趸跃跄跖跞践跶跷跸跹跻踌踪踬踯蹑蹒蹰蹿躏躜躯輼车轧轨轩轪轫转轭轮软轰轱轲轳轴轵轶轷轸轹轺轻轼载轾轿辀辁辂较辄辅辆辇辈辉辊辋辌辍辎辏辐辑辒输辔辕辖辗辘辙辚辞辟辩辫边辽达迁过迈运还这进远违连迟迩迳迹适选逊递逦逻遗遥邓邝邬邮邹邺邻郁郏郐郑郓郦郧郸酂酝酦酱酽酾酿醖采释里鉴銮錾钅钆钇针钉钊钋钌钍钎钏钐钑钒钓钔钕钖钗钘钙钚钛钜钝钞钟钠钡钢钣钤钥钦钧钨钩钪钫钬钭钮钯钰钱钲钳钴钵钶钷钸钹钺钻钼钽钾钿铀铁铂铃铄铅铆铇铈铉铊铋铌铍铎铏铐铑铒铓铔铕铖铗铘铙铚铛铜铝铞铟铠铡铢铣铤铥铦铧铨铩铪铫铬铭铮铯铰铱铲铳铴铵银铷铸铹铺铻铼铽链铿销锁锂锃锄锅锆锇锈锉锊锋锌锍锎锏锐锑锒锓锔锕锖锗锘错锚锛锜锝锞锟锠锡锢锣锤锥锦锧锨锩锪锫锬锭键锯锰锱锲锳锴锵锶锷锸锹锺锻锼锽锾锿镀镁镂镃镄镅镆镇镈镉镊镋镌镍镎镏镐镑镒镓镔镕镖镗镘镙镚镛镜镝镞镟镠镡镢镣镤镥镦镧镨镩镪镫镬镭镮镯镰镱镲镳镴镵镶长门闩闪闫闬闭问闯闰闱闲闳间闵闶闷闸闹闺闻闼闽闾闿阀阁阂阃阄阅阆阇阈阉阊阋阌阍阎阏阐阑阒阓阔阕阖阗阘阙阚阛队阳阴阵阶际陆陇陈陉陕陦陧陨险随隐隶隽难雇雏雠雳雾霁霉霡霭靓靔静靥鞑鞒鞯鞲韦韧韨韩韪韫韬韵页顶顷顸项顺须顼顽顾顿颀颁颂颃预颅领颇颈颉颊颋颌颍颎颏颐频颒颓颔颕颖颗题颙颚颛颜额颞颟颠颡颢颣颤颥颦颧风飏飐飑飒飓飔飕飖飗飘飙飚飞飨餍饣饤饥饦饧饨饩饪饫饬饭饮饯饰饱饲饳饴饵饶饷饸饹饺饻饼饽饾饿馀馁馂馃馄馅馆馇馈馉馊馋馌馍馎馏馐馑馒馓馔馕马驭驮驯驰驱驲驳驴驵驶驷驸驹驺驻驼驽驾驿骀骁骂骃骄骅骆骇骈骉骊骋验骍骎骏骐骑骒骓骔骕骖骗骘骙骚骛骜骝骞骟骠骡骢骣骤骥骦骧髅髋髌鬓鬶魇魉鱼鱽鱾鱿鲀鲁鲂鲄鲅鲆鲇鲈鲉鲊鲋鲌鲍鲎鲏鲐鲑鲒鲓鲔鲕鲖鲗鲘鲙鲚鲛鲜鲝鲞鲟鲠鲡鲢鲣鲤鲥鲦鲧鲨鲩鲪鲫鲬鲭鲮鲯鲰鲱鲲鲳鲴鲵鲶鲷鲸鲹鲺鲻鲼鲽鲾鲿鳀鳁鳂鳃鳄鳅鳆鳇鳈鳉鳊鳋鳌鳍鳎鳏鳐鳑鳒鳓鳔鳕鳖鳗鳘鳙鳛鳜鳝鳞鳟鳠鳡鳢鳣鸟鸠鸡鸢鸣鸤鸥鸦鸧鸨鸩鸪鸫鸬鸭鸮鸯鸰鸱鸲鸳鸴鸵鸶鸷鸸鸹鸺鸻鸼鸽鸾鸿鹀鹁鹂鹃鹄鹅鹆鹇鹈鹉鹊鹋鹌鹍鹎鹏鹐鹑鹒鹓鹔鹕鹖鹗鹘鹙鹚鹛鹜鹝鹞鹟鹠鹡鹢鹣鹤鹥鹦鹧鹨鹩鹪鹫鹬鹭鹯鹰鹱鹲鹳鹴鹾麦麸麹麺麽黄黉黡黩黪黾鼋鼌鼍鼹齐齑齿龀龁龂龃龄龅龆龇龈龉龊龋龌龙龚龛龟鿒鿔";
const stTo = "萬與醜專業叢東絲丟兩嚴喪個豐臨爲麗舉麼義烏樂喬習鄉書買亂爭於虧雲亙亞產畝親褻嚲億僅僕從侖倉儀們價衆優夥會傴傘偉傳俥俔傷倀倫傖僞佇體餘傭僉俠侶僥偵側僑儈儕儂儘俁儔儼倆儷倈儉債傾傯僂僨償儎儻儐儲儺兒兌兗黨蘭關興茲養獸囅內岡冊寫軍農馮衝決況凍淨悽準涼減湊凜幾鳳鳧憑凱兇擊鑿芻劃劉則剛創刪別剗剄剎劊劌剴劑剮劍剝劇勸辦務勱動勵勁勞勢勳勩勻匭匱區醫華協單賣佔盧滷臥衛卻巹廠廳歷厲壓厭厙龎廁釐廂厴廈廚廄廝縣叄參靉靆雙發變敘疊臺葉號嘆嘰籲喫後嚇呂嗎噸聽啓吳吶嘸囈嘔嚦唄員咼嗆嗚詠嚨嚀噝吒諮鹹響啞噠嘵嗶噦譁噲嚌噥喲脣嘜嗊嘮啢嗩喚嘖嗇囀齧嘓囉嘽嘯噴嘍嚳囁噯噓嚶囑嚕囂團園囪圍圇國圖圓聖壙場壞塊堅壇壢壩塢墳墜壟壠壚壘墾堊墊埡墶壋塏堖塒壎堝塹墮壪牆壯聲殼壺壼處備復夠頭誇夾奪奩奐奮獎奧妝婦媽嫵嫗嬀姍奼婁婭嬈嬌孌娛媧嫺嫿嬰嬋嬸媼嬃嬡嬪嬙嬤孫學孿寧寶實寵審憲宮寬賓寢對尋導壽將爾塵嘗堯尷屍盡層屓屜屆屬屢屨嶼歲豈嶇崗峴嵐島巖嶺嶽崬巋嶨嶧峽嶢嶠崢巒峯嶗崍嶮嶄嶸嶔嶁巔鞏巰幣帥師幃帳簾幟帶幀幫幬幘幗冪幹並廣莊慶牀廬廡庫應廟龐廢廎廩開異棄弒張彌弳彎彈強歸當錄彠彥彲徹徵徑徠憶懺憂愾懷態慫憮慪悵愴憐總懟懌戀恆懇惡慟懨愷惻惱惲悅愨懸慳悞憫驚懼慘懲憊愜慚憚慣慍憤憒願懾憖懣懶懍戇戔戲戧戰戩戱戶撲託執擴捫掃揚擾撫拋摶摳掄搶護報擔擬攏揀擁攔擰撥擇掛摯攣掗撾撻挾撓擋撟掙擠揮撏挩撈損撿換搗據擄摑擲撣摻摜攬搵撳攙擱摟揯攪攜攝攄擺搖擯攤攖撐攆擷擼攛擻攢敵敓斂斆數齋斕鬥斬斷無舊時曠暘曇暱晝曨顯晉曬曉曄暈暉暫曖術樸機殺雜權槓條來楊榪傑極構樅樞棗櫪梘棖槍楓梟櫃檸檉梔柵標棧櫛櫳棟櫨櫟欄樹棲慄樣欒椏橈楨檔榿橋樺檜槳樁樳夢檮棶槤檢梲欞槨槼櫝槧槶欏樿橢槮樓欖榲櫬櫚櫸樧檟檻檳櫧橫檣櫻櫫櫥櫓櫞檁歡歟歐殲歿殤殘殞殮殫殯毆毀轂畢斃氈毿氌氣氫氬氳匯漢湯洶澐溝沒灃漚瀝淪滄渢潙滬濘淚澩瀧瀘濼瀉潑澤涇潔灑窪浹淺漿澆湞溮濁測澮濟瀏滻渾滸濃潯濜塗湧涗濤澇淶漣潿渦溳渙滌潤澗漲澀澱淵淥漬瀆漸澠漁瀋滲溫遊灣溼濚潰濺漵漊潷滾滯灩灄滿瀅濾濫灤濱灘澦瀠瀟瀲濰潛瀦瀂瀾瀨瀕灝滅燈靈竈災燦煬爐燉煒熗點煉熾爍爛烴燭煙煩燒燁燴燙燼熱煥燜燾熅燻愛爺牘犛牽犧犢狀獷獁猶狽獮獰獨狹獅獪猙獄猻獫獵獼玀豬貓蝟獻獺璣璵瑒瑪瑋環現瑲璽琺瓏璫琿璡璉瑣瓊瑤璦璸瓔瓚甕甌電畫暢疇癤療瘧癘瘍癧瘲瘡瘋皰痾癰痙癢瘂癆瘓癇癡癉瘮瘞瘻癟癱癮癭癩癬癲皁皚皺皸盞鹽監蓋盜盤瞘眥矓睜睞瞼瞶瞞矚矯磯礬礦碭碼磚硨硯碸礪礱礫礎硜碩硤磽磑礄確磠礆礙磧磣鹼禮禡禕禰禎禱禍稟祿禪離禿稈種祕積稱穢穠穭稅穌穩穡穭窮竊竅窵窯竄窩窺竇窶豎競篤筍筆筧箋籠籩築篳篩簹箏籌篔籤篠簡籙簀篋籜籮簞簫簣簍籃籛籬籪籟糴類秈糶糲粵糞糧糉糝餱餈緊縶縕緪糹糾紆紅紂纖紇約級紈纊紀紉緯紜紘純紕紗綱納紝縱綸紛紙紋紡紵紖紐紓線紺紲紱練組紳細織終縐絆紼絀紹繹經紿綁絨結絝繞絰絎繪給絢絳絡絕絞統綆綃絹繡綌綏絛繼綈績緒綾緓續綺緋綽鞝緄繩維綿綬繃綢綯綹綣綜綻綰綠綴緇緙緗緘緬纜緹緲緝縕繢緦綞緞緶線緱縋緩締縷編緡緣縉縛縟縝縫縗縞纏縭縊縑繽縹縵縲纓縮繆繅纈繚繕繒繮繾繰繯繳纘罌網羅罰罷羆羈羥羨羣翹翽翬耮耬聳恥聶聾職聹聯聵聰肅腸膚骯餚腎腫脹脅膽勝朧腖臚脛膠脈膾髒臍腦膿臠腳脫腡臉臘醃膕齶膩靦膃騰臏羶臢輿艤艦艙艫艱豔藝節羋薌蕪蘆蓯葦藶莧萇蒼苧蘇薴蘋範莖蘢蔦塋煢繭荊薦薘莢蕘蓽萴蕎薈薺蕩榮葷滎犖熒蕁藎蓀蔭蕒葒葤藥蒞萊蓮蒔萵薟獲蕕瑩鶯蓴蘀蘿螢營縈蕭薩蔥蒕蕆蕢蔣蔞醟藍薊蘺蕷鎣驀虆薔蘞藺藹薀蘄蘊藪蘚蘊櫱虜慮虛蟲虯蟣蝨雖蝦蠆蝕蟻螞蠁蠶蠔蜆蠱蠣蟶蠻蟄蛺蟯螄蠐蛻蝸蠟蠅蟈蟬蠍螻蠑螿蟎蠨釁銜補襯袞襖嫋褘襪襲襏裝襠褌褳襝褲襉褸襤襴見觀覎規覓視覘覽覺覬覡覿覥覦覯覲覷觴觸觶誾讋譽謄訁計訂訃認譏訐訌討讓訕訖託訓議訊記訒講諱謳詎訝訥許訛論訩訟諷設訪訣證詁訶評詛識詗詐訴診詆謅詞詘詔詖譯詒誆誄試詿詩詰詼誠誅詵話誕詬詮詭詢詣諍該詳詫諢詡譸誡誣語誚誤誥誘誨誑說誦誒請諸諏諾讀諑誹課諉諛誰諗調諂諒諄誶談讅誼謀諶諜謊諫諧謔謁謂諤諭諼讒諮諳諺諦謎諞諝謨讜謖謝謠謗諡謙謐謹謾謫譾謬譚譖譙讕譜譎讞譴譫讖豶貝貞負貟貢財責賢敗賬貨質販貪貧貶購貯貫貳賤賁貰貼貴貺貸貿費賀貽賊贄賈賄貲賃賂贓資賅贐賕賑賚賒賦賭齎贖賞賜贔賙賡賠賧賴賵贅賻賺賽賾贗贊贇贈贍贏贛赬趙趕趨趲躉躍蹌蹠躒踐躂蹺蹕躚躋躊蹤躓躑躡蹣躕躥躪躦軀轀車軋軌軒軑軔轉軛輪軟轟軲軻轤軸軹軼軤軫轢軺輕軾載輊轎輈輇輅較輒輔輛輦輩輝輥輞輬輟輜輳輻輯轀輸轡轅轄輾轆轍轔辭闢辯辮邊遼達遷過邁運還這進遠違連遲邇逕跡適選遜遞邐邏遺遙鄧鄺鄔郵鄒鄴鄰鬱郟鄶鄭鄆酈鄖鄲酇醞醱醬釅釃釀醞採釋裏鑑鑾鏨釒釓釔針釘釗釙釕釷釺釧釤鈒釩釣鍆釹鍚釵鈃鈣鈈鈦鉅鈍鈔鍾鈉鋇鋼鈑鈐鑰欽鈞鎢鉤鈧鈁鈥鈄鈕鈀鈺錢鉦鉗鈷鉢鈳鉕鈽鈸鉞鑽鉬鉭鉀鈿鈾鐵鉑鈴鑠鉛鉚鉋鈰鉉鉈鉍鈮鈹鐸鉶銬銠鉺鋩錏銪鋮鋏鋣鐃銍鐺銅鋁銱銦鎧鍘銖銑鋌銩銛鏵銓鎩鉿銚鉻銘錚銫鉸銥鏟銃鐋銨銀銣鑄鐒鋪鋙錸鋱鏈鏗銷鎖鋰鋥鋤鍋鋯鋨鏽銼鋝鋒鋅鋶鐦鐧銳銻鋃鋟鋦錒錆鍺鍩錯錨錛錡鍀錁錕錩錫錮鑼錘錐錦鑕鍁錈鍃錇錟錠鍵鋸錳錙鍥鍈鍇鏘鍶鍔鍤鍬鍾鍛鎪鍠鍰鎄鍍鎂鏤鎡鐨鎇鏌鎮鎛鎘鑷钂鐫鎳鎿鎦鎬鎊鎰鎵鑌鎔鏢鏜鏝鏍鏰鏞鏡鏑鏃鏇鏐鐔钁鐐鏷鑥鐓鑭鐠鑹鏹鐙鑊鐳鐶鐲鐮鐿鑔鑣鑞鑱鑲長門閂閃閆閈閉問闖閏闈閒閎間閔閌悶閘鬧閨聞闥閩閭闓閥閣閡閫鬮閱閬闍閾閹閶鬩閿閽閻閼闡闌闃闠闊闋闔闐闒闕闞闤隊陽陰陣階際陸隴陳陘陝隯隉隕險隨隱隸雋難僱雛讎靂霧霽黴霢靄靚靝靜靨韃鞽韉韝韋韌韍韓韙韞韜韻頁頂頃頇項順須頊頑顧頓頎頒頌頏預顱領頗頸頡頰頲頜潁熲頦頤頻頮頹頷頴穎顆題顒顎顓顏額顳顢顛顙顥纇顫顬顰顴風颺颭颮颯颶颸颼颻飀飄飆飈飛饗饜飠飣飢飥餳飩餼飪飫飭飯飲餞飾飽飼飿飴餌饒餉餄餎餃餏餅餑餖餓餘餒餕餜餛餡館餷饋餶餿饞饁饃餺餾饈饉饅饊饌饢馬馭馱馴馳驅馹駁驢駔駛駟駙駒騶駐駝駑駕驛駘驍罵駰驕驊駱駭駢驫驪騁驗騂駸駿騏騎騍騅騌驌驂騙騭騤騷騖驁騮騫騸驃騾驄驏驟驥驦驤髏髖髕鬢鬹魘魎魚魛魢魷魨魯魴魺鮁鮃鮎鱸鮋鮓鮒鮊鮑鱟鮍鮐鮭鮚鮳鮪鮞鮦鰂鮜鱠鱭鮫鮮鮺鯗鱘鯁鱺鰱鰹鯉鰣鰷鯀鯊鯇鮶鯽鯒鯖鯪鯕鯫鯡鯤鯧鯝鯢鯰鯛鯨鰺鯴鯔鱝鰈鰏鱨鯷鰮鰃鰓鱷鰍鰒鰉鰁鱂鯿鰠鰲鰭鰨鰥鰩鰟鰜鰳鰾鱈鱉鰻鰵鱅鰼鱖鱔鱗鱒鱯鱤鱧鱣鳥鳩雞鳶鳴鳲鷗鴉鶬鴇鴆鴣鶇鸕鴨鴞鴦鴒鴟鴝鴛鷽鴕鷥鷙鴯鴰鵂鴴鵃鴿鸞鴻鵐鵓鸝鵑鵠鵝鵒鷳鵜鵡鵲鶓鵪鵾鵯鵬鵮鶉鶊鵷鷫鶘鶡鶚鶻鶖鷀鶥鶩鷊鷂鶲鶹鶺鷁鶼鶴鷖鸚鷓鷚鷯鷦鷲鷸鷺鸇鷹鸌鸏鸛鸘鹺麥麩麴麪麼黃黌黶黷黲黽黿鼂鼉鼴齊齏齒齔齕齗齟齡齙齠齜齦齬齪齲齷龍龔龕龜鿓鎶";
const charMaps = {};

function convertChinese(text, to) {
  charMaps[to] ||= to === "simplified"
    ? new Map([...tsFrom].map((c, i) => [c, tsTo[i]]))
    : new Map([...stFrom].map((c, i) => [c, stTo[i]]));
  return text.replace(/[一-鿿]/g, (c) => charMaps[to].get(c) || c);
}

const curatedKey = (text) => convertChinese(normalizeMatchText(text), "simplified");

// A channel's own search matches titles in the script the query is written
// in, so the song is searched for in both.
async function searchChannel(channelId, name) {
  const queries = [...new Set([name, convertChinese(name, "simplified"), convertChinese(name, "traditional")])];
  const results = await Promise.all(queries.map(async (query) => {
    // The channel's Search tab.
    const res = await webCall("browse", { browseId: channelId, params: "EgZzZWFyY2jyBgQKAloA", query });
    return findAll(res, "videoRenderer").map((video) => ({
      videoId: video.videoId,
      title: textOf(video.title),
      durationMs: msOf(textOf(video.lengthText)),
    }));
  }));
  return results.flat();
}

const playlistMaxPages = 20;
const playlistMaxAgeMs = 24 * 60 * 60 * 1000;
const pendingPlaylists = new Map();

async function fetchPlaylist(playlistId) {
  const videos = [];
  let res = await webCall("browse", { browseId: `VL${playlistId}` });
  for (let pages = 1; res; pages += 1) {
    // The videos and the next page's token share one array; the page's other
    // continuations belong to its menus.
    const items = findAll(res, "itemSectionRenderer").flatMap((s) => s.contents || [])
      .concat(findAll(res, "appendContinuationItemsAction").flatMap((a) => a.continuationItems || []));
    for (const item of items) {
      const lockup = item.lockupViewModel;
      if (lockup?.contentType !== "LOCKUP_CONTENT_TYPE_VIDEO") continue;
      videos.push({
        videoId: lockup.contentId,
        title: lockup.metadata?.lockupMetadataViewModel?.title?.content || "",
        durationMs: msOf(findAll(lockup.contentImage, "thumbnailBadgeViewModel")[0]?.text),
      });
    }
    const token = findAll(items.find((item) => item.continuationItemRenderer), "continuationCommand")[0]?.token;
    if (!token || pages >= playlistMaxPages) break;
    res = await webCall("browse", { continuation: token });
  }
  return videos.filter((video) => video.videoId && video.title);
}

// Playlists are kept for a day; when one can't be fetched, the last copy is
// used.
async function playlistVideos(playlistId) {
  const key = `playlist:${playlistId}`;
  const stored = host.storage.get(key);
  if (stored && Date.now() - stored.at < playlistMaxAgeMs) return stored.videos;
  let pending = pendingPlaylists.get(key);
  if (!pending) {
    pending = fetchPlaylist(playlistId)
      .then((videos) => {
        host.storage.set(key, { at: Date.now(), videos });
        return videos;
      })
      .finally(() => pendingPlaylists.delete(key));
    pendingPlaylists.set(key, pending);
  }
  return pending.catch((e) => {
    console.warn(`playlist ${playlistId}:`, e.message);
    return stored?.videos || [];
  });
}

// The song names a fan upload's title may carry: "artist－song",
// "artist：song", "song — original artist (Cover by …)", or "…《song》…".
function curatedTitleKeys(title, artists) {
  let text = title.normalize("NFKC").trim().replace(/^【[^】]*】\s*/u, "");
  const keys = [...text.matchAll(/《([^》]+)》/gu)].map((m) => m[1]);
  for (const artist of artists) {
    if (text.startsWith(artist)) text = text.slice(artist.length).replace(/^\s*[-–—:|]\s*/u, "");
  }
  keys.push(text.split(/\s*[-–—:|~]\s*/u)[0].split(/\s*[(（]/u)[0]);
  return keys.map(curatedKey).filter(Boolean);
}

// The target's name with and without what follows " - " or a bracket, as in
// "Song - Live" or "Song (Cover)".
function curatedTargetKeys(name) {
  const text = name.normalize("NFKC").trim();
  const base = text.split(/\s+[-–—]\s+/u)[0].split(/\s*[(（[【]/u)[0];
  return [...new Set([text, base].map(curatedKey).filter(Boolean))];
}

// The closest-length curated upload whose title names the song, or null when
// the target's artists have no curated sources or nothing in them matches.
async function matchCurated(target) {
  const sources = curatedSources.filter((source) => source.artists.some((name) => target.artists.includes(name)));
  if (!sources.length) return null;
  const query = target.name.split(/\s+[-–—]\s+/u)[0].split(/\s*[(（[【]/u)[0].trim() || target.name;
  const targetKeys = curatedTargetKeys(target.name);
  const lookups = sources.flatMap((source) => [
    ...source.channels.map((id) => ({ artists: source.artists, videos: searchChannel(id, query) })),
    ...source.playlists.map((id) => ({ artists: source.artists, videos: playlistVideos(id) })),
  ]);
  const found = await Promise.all(lookups.map(async ({ artists, videos }) => {
    try {
      return (await videos).filter((video) => curatedTitleKeys(video.title, artists).some((key) => targetKeys.includes(key)));
    } catch (e) {
      console.warn("curated search failed:", e.message);
      return [];
    }
  }));
  const distance = (video) => (video.durationMs && target.durationMs
    ? Math.abs(video.durationMs - target.durationMs)
    : Infinity);
  const best = found.flat().sort((a, b) => distance(a) - distance(b))[0];
  return best ? { candidate: { ...best, author: "", curated: true } } : null;
}

async function matchSpotifyTrack(id) {
  const res = await gql("getTrack", "612585ae06ba435ad26369870deaae23b5c8800a256cd8a57e08eddc25a37294", {
    uri: `spotify:track:${id}`,
  });
  const tData = res?.data?.trackUnion;
  if (!tData) throw fail("unavailable", t("track not found"));
  const name = tData.name || "";
  const artistItems = [
    ...(tData.firstArtist?.items || []),
    ...(tData.otherArtists?.items || []),
  ];
  const spotifyArtists = [...new Set(artistItems.map((item) => item?.profile?.name).filter(Boolean))];
  const artist = spotifyArtists[0] || "";
  const artists = withAliases(spotifyArtists);
  const durationMs = tData.duration?.totalMilliseconds || 0;
  const target = { id, name, artist, artists, durationMs };

  const curated = await matchCurated(target);
  if (curated) return curated;

  // Searches run in rounds, most precise first; the queries within a round run
  // together.
  const searchSpecs = [
    { round: 0, type: "music", query: `${name} ${artist}`.trim(), artistTitle: true },
    { round: 1, type: "music", query: name.trim(), artistTitle: false },
    { round: 1, type: "youtube", query: `${artist} ${name} official`.trim(), artistTitle: true },
    { round: 2, type: "youtube", query: `${name} ${artist}`.trim(), artistTitle: true },
    { round: 2, type: "youtube", query: name.trim(), artistTitle: false },
  ].filter((item) => item.query);
  const uniqueSpecs = [...new Map(searchSpecs.map((item) => [`${item.type}:${normalizeMatchText(item.query)}`, item])).values()];
  const candidateMap = new Map();
  const pickBest = () => {
    const scored = [...candidateMap.values()]
      .map((candidate) => ({ candidate, ...scoreCandidate(candidate, target) }))
      .filter((item) => item.eligible)
      // Tiers first, whatever the scores: a third-party upload only wins when
      // no official upload ties to the artist.
      .sort((a, b) => a.tier - b.tier || b.score - a.score);
    return scored[0] || null;
  };
  // Stop as soon as a round turns up a confident match: firing every query
  // for every track (preloads, quick skips) bursts enough requests to get
  // rate limited by YouTube.
  const rounds = [...new Set(uniqueSpecs.map((spec) => spec.round))];
  for (const round of rounds) {
    const specs = uniqueSpecs.filter((spec) => spec.round === round);
    const results = await Promise.allSettled(specs.map((spec) => spec.type === "music"
      ? searchSongs(spec.query)
      : searchYouTubeVideos(spec.query)));
    results.forEach((result, index) => {
      if (result.status === "fulfilled") addCandidatesTo(candidateMap, specs[index], result.value);
      else console.warn("YouTube candidate search failed:", result.reason?.message || result.reason);
    });
    const best = pickBest();
    if (best?.confident) return best;
  }
  return pickBest();
}

// Merges one search's results into the candidates seen so far, keeping the
// best rank and every official signal each video picked up.
function addCandidatesTo(candidateMap, spec, results) {
  for (const candidate of results) {
    const existing = candidateMap.get(candidate.videoId);
    if (existing) {
      existing.catalogResult ||= candidate.catalogResult === true;
      if (spec.artistTitle) existing.artistTitleSearchRank = Math.min(existing.artistTitleSearchRank ?? 999, candidate.rank ?? 999);
      else existing.titleSearchRank = Math.min(existing.titleSearchRank ?? 999, candidate.rank ?? 999);
      existing.officialBadge ||= candidate.officialBadge === true;
      existing.topicOfficial ||= candidate.topicOfficial === true;
      existing.viewCount = Math.max(existing.viewCount || 0, candidate.viewCount || 0);
    } else {
      candidateMap.set(candidate.videoId, {
        ...candidate,
        artistTitleSearchRank: spec.artistTitle ? (candidate.rank ?? 999) : 999,
        titleSearchRank: spec.artistTitle ? 999 : (candidate.rank ?? 999),
        queryEvidence: [spec.query],
      });
    }
  }
}

// Concurrent requests for the same track (a preload racing playback) share
// one search instead of each running their own.
const pendingMatches = new Map();

async function getMatchedVideoId(id) {
  const cacheKey = `yt:v24:${id}`;
  const cached = host.storage.get(cacheKey);
  if (cached) return cached;
  let pending = pendingMatches.get(id);
  if (!pending) {
    pending = matchSpotifyTrack(id).finally(() => pendingMatches.delete(id));
    pendingMatches.set(id, pending);
  }
  const match = await pending;
  if (!match || !match.candidate?.videoId) {
    throw fail("unavailable", t("could not find audio on YouTube"));
  }
  const videoId = match.candidate.videoId;
  host.storage.set(cacheKey, videoId);
  return videoId;
}

const installed = {};

async function program(name, versionFlag) {
  if (installed[name]) return installed[name];
  const places = [name, `/opt/homebrew/bin/${name}`, `/usr/local/bin/${name}`];
  for (const path of places) {
    try {
      const proc = host.spawn(path, [versionFlag]);
      proc.closeStdin();
      while ((await proc.readLine()) !== null) {}
      if ((await proc.wait()) === 0) {
        installed[name] = path;
        return path;
      }
    } catch (e) {
      if (/allowed/.test(e.message)) {
        throw fail("setup", t("Allow MyGotify to start programs in its settings"));
      }
    }
  }
  return null;
}

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

const located = new Map();
const locatedFor = 60 * 60 * 1000;

async function locate(id) {
  const known = located.get(id);
  if (known && Date.now() - known.at < locatedFor) return known;
  let found;
  try {
    found = await direct(id);
  } catch (e) {
    // VisionOS can reject videos that yt-dlp can still play.
    console.warn(`finding ${id}'s audio: ${e.message}`);
    visitor = "";
    found = await throughYtdlp(id, e);
  }
  found.at = Date.now();
  located.set(id, found);
  return found;
}

let visitor = "";

async function visitorData() {
  if (visitor) return visitor;
  const r = await ytCall("visitor_id", {}, { ...remix, anonymous: true });
  visitor = r.responseContext?.visitorData || "";
  if (!visitor) throw new Error(t("YouTube gave this visit no ID"));
  return visitor;
}

async function direct(id) {
  const r = await ytCall("player", { videoId: id, contentCheckOk: true, racyCheckOk: true }, visionOS(await visitorData()));
  const status = r.playabilityStatus || {};
  if (status.status !== "OK") {
    const why = status.reason || `YouTube says ${status.status || "nothing"} of this`;
    throw status.status === "UNPLAYABLE" || status.status === "ERROR" ? fail("unavailable", why) : new Error(why);
  }
  let best = null;
  for (const f of r.streamingData?.adaptiveFormats || []) {
    if (!f.mimeType?.startsWith("audio/") || !f.url || f.isDrc) continue;
    if (f.audioTrack && !f.audioTrack.audioIsDefault) continue;
    if (!best || f.bitrate > best.bitrate) best = f;
  }
  if (!best) throw new Error(t("YouTube listed no audio to play as it is"));
  return { url: best.url, http_headers: { "User-Agent": webUA }, gain: gainOf(r.playerConfig?.audioConfig), direct: true };
}

function gainOf(audio) {
  const lkfs = audio?.trackAbsoluteLoudnessLkfs ?? audio?.perceptualLoudnessDb;
  if (typeof lkfs !== "number" || !lkfs) return undefined;
  return Math.round((-18 - lkfs) * 100) / 100;
}

const ytdlpTimeout = 25000;

async function throughYtdlp(id, why) {
  const ytdlp = await program("yt-dlp", "--version");
  if (!ytdlp) throw why;
  const args = [
    "--config-locations",
    "-",
    "--no-warnings",
    "--no-playlist",
    "--no-progress",
    "--extractor-args",
    "youtube:skip=hls,dash",
    "--format",
    "bestaudio[protocol^=http]/bestaudio",
    "--print",
    "%(.{url,http_headers})j",
  ];
  for (const rt of ["deno", "node", "bun"]) {
    const path = await program(rt, "--version");
    if (path) {
      args.push("--js-runtimes", `${rt}:${path}`);
      break;
    }
  }
  args.push(`https://www.youtube.com/watch?v=${id}`);

  const proc = host.spawn(ytdlp, args);
  proc.closeStdin();
  const timer = setTimeout(() => proc.kill(), ytdlpTimeout);
  const lines = [];
  for (let line; (line = await proc.readLine()) !== null; ) lines.push(line);
  const code = await proc.wait();
  clearTimeout(timer);
  if (code !== 0 || !lines.length) throw ytdlpFailure(proc.errorOutput());
  return { ...JSON.parse(lines[lines.length - 1]), direct: false };
}

function ytdlpFailure(output) {
  const said = output.split("\n").reverse().find((l) => l.startsWith("ERROR:")) || output.trim() || "yt-dlp stopped";
  const why = said.replace(/^ERROR:\s*(\[[^\]]*\]\s*)?(\S+:\s*)?/, "");
  if (/not a bot|sign in|cookies/i.test(why)) {
    return fail("signIn", t("YouTube asks you to sign in to play this"));
  }
  if (/unavailable|private|removed|not available|premium/i.test(why)) return fail("unavailable", why);
  return new Error(why);
}

let ranged = null;

async function asksInPieces(ffmpeg) {
  if (ranged !== null) return ranged;
  const proc = host.spawn(ffmpeg, ["-hide_banner", "-h", "protocol=http"]);
  proc.closeStdin();
  let found = false;
  for (let line; (line = await proc.readLine()) !== null; ) found ||= line.includes("-request_size");
  await proc.wait();
  return (ranged = found);
}

const serving = [];
const servingAtMost = 3;
const servedWithin = 10 * 60 * 1000;
const portTries = 3;
const listenSettle = 300;

// ffmpeg prints "Output #0" once a player has connected to its listener, so the
// ones without it are still waiting: drop those first, oldest first, and only
// cut off a connected one (the track playing) when every slot is connected.
function stopWaiting() {
  while (serving.length >= servingAtMost) {
    const victim = serving.find((p) => !p.errorOutput().includes("Output #0")) || serving[0];
    serving.splice(serving.indexOf(victim), 1);
    victim.kill();
  }
}

async function serve(source, bitRate) {
  const ffmpeg = await program("ffmpeg", "-version");
  if (!ffmpeg) {
    throw fail("setup", t("MyGotify plays audio through ffmpeg: install it with Homebrew, or so that it's on the PATH"));
  }
  const pieces = await asksInPieces(ffmpeg);
  for (let tries = 1; ; tries++) {
    try {
      return await serveOn(20000 + Math.floor(Math.random() * 40000), ffmpeg, pieces, source, bitRate);
    } catch (e) {
      if (!e.portTaken || tries >= portTries) throw e;
    }
  }
}

async function serveOn(port, ffmpeg, pieces, source, bitRate) {
  stopWaiting();
  const headers = source.http_headers || {};
  const proc = host.spawn(ffmpeg, [
    "-nostdin",
    "-hide_banner",
    "-nostats",
    "-reconnect",
    "1",
    "-reconnect_streamed",
    "1",
    "-reconnect_delay_max",
    "5",
    "-rw_timeout",
    "15000000",
    ...(pieces ? ["-request_size", String(10 << 20)] : []),
    ...(headers["User-Agent"] ? ["-user_agent", headers["User-Agent"]] : []),
    "-i",
    source.url,
    "-vn",
    "-c:a",
    "libmp3lame",
    "-b:a",
    `${bitRate}k`,
    "-id3v2_version",
    "0",
    "-write_xing",
    "0",
    "-f",
    "mp3",
    "-listen",
    "1",
    `http://127.0.0.1:${port}/`,
  ]);
  proc.closeStdin();
  let stopped = false;
  serving.push(proc);
  const timer = setTimeout(() => proc.kill(), servedWithin);
  proc.wait().then(() => {
    stopped = true;
    clearTimeout(timer);
    const at = serving.indexOf(proc);
    if (at >= 0) serving.splice(at, 1);
  });
  const stoppedEarly = () => {
    const said = proc.errorOutput();
    const e = new Error(`ffmpeg stopped: ${said.trim().split("\n").pop()}`);
    e.portTaken = /address already in use/i.test(said);
    return e;
  };

  const until = Date.now() + 15000;
  while (!proc.errorOutput().includes("Input #0")) {
    if (stopped) throw stoppedEarly();
    if (Date.now() > until) {
      proc.kill();
      throw new Error(t("the audio didn't start in time"));
    }
    await sleep(30);
  }
  // ffmpeg opens its listener right after reading the input but logs nothing once
  // it is bound, and connecting to check would use up its single client. So give
  // it a moment and hand the address over only if ffmpeg is still running then:
  // a taken port or any other failure to listen makes it exit straight away.
  const settled = Date.now() + listenSettle;
  while (Date.now() < settled) {
    if (stopped) throw stoppedEarly();
    await sleep(30);
  }
  if (stopped) throw stoppedEarly();
  return `http://127.0.0.1:${port}/`;
}

export async function stream({ id, quality }) {
  const kbps = quality === "standard" ? 128 : 192;
  const videoId = await getMatchedVideoId(id);
  let source = await locate(videoId);
  let url;
  try {
    url = await serve(source, kbps);
  } catch (e) {
    located.delete(videoId);
    if (!source.direct || e.code === "setup") throw e;
    console.warn(`playing ${videoId} as YouTube gave it: ${e.message}`);
    source = { ...(await throughYtdlp(videoId, e)), gain: source.gain, at: Date.now() };
    url = await serve(source, kbps);
    located.set(videoId, source);
  }
  return {
    url,
    type: "mp3",
    quality: kbps === 128 ? "standard" : "high",
    bitRate: kbps * 1000,
    gain: source.gain,
  };
}
