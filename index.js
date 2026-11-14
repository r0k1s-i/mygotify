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
  const unavailable = raw.playability?.playable === false ? true : undefined;
  return {
    id,
    name,
    artists,
    album,
    duration,
    url,
    unavailable,
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

async function searchYouTubeVideos(query) {
  const date = new Date().toISOString().slice(0, 10).replaceAll("-", "");
  const res = await fetch("https://www.youtube.com/youtubei/v1/search?prettyPrint=false", {
    method: "POST",
    headers: {
      "content-type": "application/json",
      "user-agent": webUA,
      origin: "https://www.youtube.com",
      "x-origin": "https://www.youtube.com",
    },
    body: JSON.stringify({
      context: { client: { clientName: "WEB", clientVersion: `2.${date}.00.00`, hl: host.language() === "zh-CN" ? "zh-CN" : "en", gl: "JP" } },
      query,
    }),
  });
  if (!res.ok) throw new Error(`YouTube search: ${res.status}`);
  const data = await res.json();
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
  let score = c.officialBadge ? 220 : (officialTopic ? 190 : (c.catalogResult ? 140 : -1000));
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
  const eligible = officialSource && !versionMismatch && (exactMatch || safeContainsMatch);
  return { score, diffSec, titleExact, artistMatch, officialSource, versionMismatch, eligible };
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
  const artists = [...new Set(artistItems.map((item) => item?.profile?.name).filter(Boolean))];
  const artist = artists[0] || "";
  const durationMs = tData.duration?.totalMilliseconds || 0;
  const target = { id, name, artist, artists, durationMs };

  const searchSpecs = [
    { type: "music", query: `${name} ${artist}`.trim(), artistTitle: true },
    { type: "music", query: name.trim(), artistTitle: false },
    { type: "youtube", query: `${artist} ${name} official`.trim(), artistTitle: true },
    { type: "youtube", query: `${name} ${artist}`.trim(), artistTitle: true },
    { type: "youtube", query: name.trim(), artistTitle: false },
  ].filter((item) => item.query);
  const uniqueSpecs = [...new Map(searchSpecs.map((item) => [`${item.type}:${normalizeMatchText(item.query)}`, item])).values()];
  const searches = uniqueSpecs.map((spec) => spec.type === "music"
    ? searchSongs(spec.query)
    : searchYouTubeVideos(spec.query));
  const results = await Promise.allSettled(searches);
  const candidateMap = new Map();
  results.forEach((result, index) => {
    if (result.status !== "fulfilled") {
      console.warn("YouTube candidate search failed:", result.reason?.message || result.reason);
      return;
    }
    const spec = uniqueSpecs[index];
    for (const candidate of result.value) {
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
  });
  const scored = [...candidateMap.values()]
    .map((candidate) => ({ candidate, ...scoreCandidate(candidate, target) }))
    .filter((item) => item.eligible)
    .sort((a, b) => b.score - a.score);
  return scored[0] || null;
}
async function getMatchedVideoId(id) {
  const cacheKey = `yt:v23:${id}`;
  const cached = host.storage.get(cacheKey);
  if (cached) return cached;
  const match = await matchSpotifyTrack(id);
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
