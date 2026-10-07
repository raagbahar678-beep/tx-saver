package com.example.myapp

import android.app.Activity
import android.app.AlertDialog
import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.ClipData
import android.content.ClipboardManager
import android.content.Context
import android.content.Intent
import android.content.pm.ServiceInfo
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.Paint
import android.graphics.PixelFormat
import android.graphics.Typeface
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.IBinder
import android.os.Looper
import android.os.ParcelFileDescriptor
import android.provider.DocumentsContract
import android.provider.OpenableColumns
import android.provider.Settings
import android.text.InputType
import android.text.TextUtils
import android.util.TypedValue
import android.view.ContextThemeWrapper
import android.view.Gravity
import android.view.HapticFeedbackConstants
import android.view.InputDevice
import android.view.KeyCharacterMap
import android.view.KeyEvent
import android.view.MotionEvent
import android.view.PointerIcon
import android.view.ScaleGestureDetector
import android.view.VelocityTracker
import android.view.View
import android.view.ViewConfiguration
import android.view.ViewGroup
import android.view.WindowManager
import android.view.inputmethod.BaseInputConnection
import android.view.inputmethod.EditorInfo
import android.view.inputmethod.ExtractedText
import android.view.inputmethod.ExtractedTextRequest
import android.view.inputmethod.InputConnection
import android.view.inputmethod.InputMethodManager
import android.widget.Button
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.HorizontalScrollView
import android.widget.LinearLayout
import android.widget.OverScroller
import android.widget.TextView
import android.widget.Toast
import java.io.BufferedOutputStream
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.IOException
import java.io.OutputStream
import java.nio.ByteBuffer
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets
import org.json.JSONArray
import org.json.JSONObject

const val CHUNK_BYTES = 65536
const val CHUNK_CHARS = 65536
const val LINE_CAP = 20000L
const val MAX_BACK = 80000L
const val UNDO_MAX = 8000000L
const val UNDO_TOTAL = 24000000L
const val INLINE_MAX = 4000000L
const val SMALL_FILE = 8388608L
const val MEM_FILE = "textpad_memory.json"

val C_BG = Color.parseColor("#1a1a2e")
val C_HEAD = Color.parseColor("#16213e")
val C_BTN = Color.parseColor("#0f3460")
val C_TXT = Color.parseColor("#c9d1d9")
val C_ED = Color.parseColor("#0d1117")
val C_GOLD = Color.parseColor("#e2b96f")
val C_SEL = Color.parseColor("#1f4068")
val C_DIM = Color.parseColor("#6e7681")
val C_NUM = Color.parseColor("#484f58")
val C_STAT = Color.parseColor("#161b22")
val C_DIV = Color.parseColor("#2a2a4a")
val C_DIVH = Color.parseColor("#4a4a8a")
val C_UR = Color.parseColor("#1a2a3a")
val C_RMBG = Color.parseColor("#3a1010")
val C_RMFG = Color.parseColor("#ff6b6b")
val C_FOLDER = Color.parseColor("#8b949e")
val C_THUMB = Color.parseColor("#30363d")

fun Context.dp(v: Int): Int = (v * resources.displayMetrics.density + 0.5f).toInt()
fun Context.dpf(v: Float): Float = v * resources.displayMetrics.density

fun countNl(s: String): Int {
    var n = 0
    for (ch in s) if (ch == '\n') n++
    return n
}

fun mkBtn(ctx: Context, text: String, bg: Int, fg: Int, sp: Float, onClick: () -> Unit): Button {
    val b = Button(ctx)
    b.text = text
    b.isAllCaps = false
    b.setTextColor(fg)
    b.setBackgroundColor(bg)
    b.textSize = sp
    b.typeface = Typeface.MONOSPACE
    b.isFocusable = false
    b.isFocusableInTouchMode = false
    b.stateListAnimator = null
    b.minWidth = 0
    b.minimumWidth = 0
    b.minHeight = 0
    b.minimumHeight = 0
    b.setPadding(ctx.dp(9), ctx.dp(5), ctx.dp(9), ctx.dp(5))
    b.setOnClickListener { onClick() }
    return b
}

interface Host {
    val isOverlay: Boolean
    fun pickFolder(panelId: Int)
    fun pickOpen(panelId: Int)
    fun toggleTop(panelId: Int)
    fun panelsChanged()
    fun dialogContext(): Context
    fun showDialog(d: AlertDialog)
    fun toast(msg: String)
}

class Chunk(val off: Long, val blen: Int, val clen: Int, val nl: Int, var text: String?, val mem: Boolean)

class Op(var pos: Long, var del: String, var ins: String, val kind: Int)

// ---------------------------------------------------------------------------
// Doc: huge-text store. Text is split into ~64K chunks. Untouched chunks stay
// on disk (read on demand, small LRU cache); edited chunks live in memory.
// ---------------------------------------------------------------------------
class Doc {
    private val chunks = ArrayList<Chunk>()
    private var starts = LongArray(64)
    private var nls = LongArray(64)
    private val cache = ArrayList<Chunk>()
    private var placeholder = true
    private var fis: FileInputStream? = null
    @Volatile var total = 0L
    @Volatile var totalNl = 0L
    @Volatile var gen = 0
    var chan: FileChannel? = null
    var pfd: ParcelFileDescriptor? = null
    var srcKey: String? = null
    @Volatile var indexing = false
    @Volatile var indexPct = 0

    init {
        chunks.add(Chunk(0L, 0, 0, 0, "", true))
        reindexFrom(0)
    }

    private fun reindexFrom(k0: Int) {
        val n = chunks.size
        if (starts.size < n + 1) {
            val ns = maxOf(n + 1, starts.size * 2)
            starts = starts.copyOf(ns)
            nls = nls.copyOf(ns)
        }
        var k = k0
        var s = if (k == 0) 0L else starts[k - 1] + chunks[k - 1].clen
        var l = if (k == 0) 0L else nls[k - 1] + chunks[k - 1].nl
        while (k < n) {
            starts[k] = s
            nls[k] = l
            s += chunks[k].clen
            l += chunks[k].nl
            k++
        }
        total = s
        totalNl = l
        gen++
    }

    private fun chunkAt(pos: Long): Int {
        var lo = 0
        var hi = chunks.size - 1
        while (lo < hi) {
            val mid = (lo + hi + 1) ushr 1
            if (starts[mid] <= pos) lo = mid else hi = mid - 1
        }
        return lo
    }

    private fun touch(c: Chunk) {
        cache.remove(c)
        cache.add(c)
        while (cache.size > 48) {
            val e = cache.removeAt(0)
            if (!e.mem) e.text = null
        }
    }

    private fun readChunk(c: Chunk): String {
        return try {
            val ch = chan ?: return " ".repeat(c.clen)
            val bb = ByteBuffer.allocate(c.blen)
            var pos = c.off
            while (bb.hasRemaining()) {
                val n = ch.read(bb, pos)
                if (n < 0) break
                pos += n
            }
            String(bb.array(), 0, bb.position(), StandardCharsets.UTF_8)
        } catch (e: Exception) {
            " ".repeat(c.clen)
        }
    }

    private fun textOf(k: Int): String {
        val c = chunks[k]
        val t = c.text
        if (t != null) {
            if (!c.mem) touch(c)
            return t
        }
        val s = readChunk(c)
        var cc = c
        if (s.length != c.clen) {
            cc = Chunk(c.off, c.blen, s.length, c.nl, null, false)
            chunks[k] = cc
            reindexFrom(k)
        }
        cc.text = s
        touch(cc)
        return s
    }

    @Synchronized
    fun getText(from0: Long, to0: Long): String {
        val from = from0.coerceIn(0L, total)
        val to = to0.coerceIn(from, total)
        if (from >= to) return ""
        val sb = StringBuilder(minOf(to - from, 1000000L).toInt())
        var k = chunkAt(from)
        var p = from
        while (p < to && k < chunks.size) {
            val s = textOf(k)
            val st = starts[k]
            val a = (p - st).toInt().coerceIn(0, s.length)
            val b = (minOf(to, st + s.length) - st).toInt().coerceIn(a, s.length)
            sb.append(s, a, b)
            p = st + b
            k++
        }
        return sb.toString()
    }

    @Synchronized
    fun charAtSafe(pos: Long): Char {
        if (pos < 0L || pos >= total) return '\u0000'
        val k = chunkAt(pos)
        val s = textOf(k)
        val i = (pos - starts[k]).toInt()
        return if (i >= 0 && i < s.length) s[i] else '\u0000'
    }

    // index of first '\n' in [from, limit) or -1
    @Synchronized
    fun indexOfNl(from0: Long, limit0: Long): Long {
        val from = from0.coerceIn(0L, total)
        val limit = limit0.coerceIn(from, total)
        if (from >= limit) return -1L
        var k = chunkAt(from)
        while (k < chunks.size) {
            if (starts[k] >= limit) return -1L
            val s = textOf(k)
            val st = starts[k]
            val a = if (from > st) (from - st).toInt() else 0
            val i = if (a <= s.length) s.indexOf('\n', a) else -1
            if (i >= 0) {
                val p = st + i
                return if (p < limit) p else -1L
            }
            k++
        }
        return -1L
    }

    // last '\n' with floor <= index < before, or -1
    @Synchronized
    fun lastIndexOfNl(before0: Long, floor0: Long): Long {
        val before = before0.coerceIn(0L, total)
        val floor = floor0.coerceIn(0L, before)
        if (before <= floor) return -1L
        var k = chunkAt(before - 1L)
        while (k >= 0) {
            val s = textOf(k)
            val st = starts[k]
            if (st + s.length <= floor) return -1L
            val endLocal = minOf(before - st, s.length.toLong()).toInt()
            if (endLocal > 0) {
                val i = s.lastIndexOf('\n', endLocal - 1)
                if (i >= 0) {
                    val p = st + i
                    return if (p >= floor) p else -1L
                }
            }
            k--
        }
        return -1L
    }

    @Synchronized
    fun nlBefore(pos0: Long): Long {
        val pos = pos0.coerceIn(0L, total)
        val k = chunkAt(pos)
        val s = textOf(k)
        val local = (pos - starts[k]).toInt().coerceIn(0, s.length)
        var cnt = 0
        for (i in 0 until local) if (s[i] == '\n') cnt++
        return nls[k] + cnt
    }

    @Synchronized
    fun replace(from0: Long, to0: Long, ins: String) {
        val from = from0.coerceIn(0L, total)
        val to = to0.coerceIn(from, total)
        val k1 = chunkAt(from)
        val s1 = textOf(k1)
        var k2 = chunkAt(to)
        if (k2 < k1) k2 = k1
        val s2 = if (k2 == k1) s1 else textOf(k2)
        val off1 = (from - starts[k1]).toInt().coerceIn(0, s1.length)
        val off2 = (to - starts[k2]).toInt().coerceIn(0, s2.length)
        val sb = StringBuilder(off1 + ins.length + (s2.length - off2))
        sb.append(s1, 0, off1)
        sb.append(ins)
        sb.append(s2, off2, s2.length)
        val full = sb.toString()
        val pieces = ArrayList<Chunk>()
        var i = 0
        while (i < full.length) {
            var e = minOf(full.length, i + CHUNK_CHARS)
            if (e < full.length && Character.isLowSurrogate(full[e]) && e - 1 > i) e--
            val sub = full.substring(i, e)
            pieces.add(Chunk(0L, 0, sub.length, countNl(sub), sub, true))
            i = e
        }
        if (pieces.isEmpty()) pieces.add(Chunk(0L, 0, 0, 0, "", true))
        chunks.subList(k1, k2 + 1).clear()
        chunks.addAll(k1, pieces)
        placeholder = false
        reindexFrom(k1)
    }

    @Synchronized
    fun chunkTextForSave(c: Chunk): String {
        val t = c.text
        return t ?: readChunk(c)
    }

    @Synchronized
    fun lineStartNear(pos0: Long): Long {
        val pos = pos0.coerceIn(0L, total)
        val floor = maxOf(0L, pos - LINE_CAP)
        val nl = lastIndexOfNl(pos, floor)
        return if (nl >= 0L) nl + 1L else floor
    }

    @Synchronized
    fun posOfLine(line0: Long): Long {
        val line = line0.coerceIn(0L, totalNl)
        var lo = 0
        var hi = chunks.size - 1
        while (lo < hi) {
            val mid = (lo + hi + 1) ushr 1
            if (nls[mid] <= line) lo = mid else hi = mid - 1
        }
        var need = line - nls[lo]
        val s = textOf(lo)
        var i = 0
        while (need > 0L) {
            val j = s.indexOf('\n', i)
            if (j < 0) break
            i = j + 1
            need--
        }
        return starts[lo] + i
    }

    @Synchronized
    fun snapshot(): ArrayList<Chunk> = ArrayList(chunks)

    @Synchronized
    fun hasBacking(): Boolean {
        if (chan == null) return false
        for (c in chunks) if (!c.mem) return true
        return false
    }

    @Synchronized
    private fun appendIndexed(list: ArrayList<Chunk>) {
        if (list.isEmpty()) return
        if (placeholder) {
            chunks.clear()
            placeholder = false
        }
        val k = chunks.size
        chunks.addAll(list)
        reindexFrom(k)
    }

    // After a save, point all chunks at the newly written file.
    @Synchronized
    fun rebase(snap: ArrayList<Chunk>, blens: IntArray, np: ParcelFileDescriptor, key: String): Boolean {
        if (snap.size != chunks.size) return false
        for (i in snap.indices) if (snap[i] !== chunks[i]) return false
        val f2 = FileInputStream(np.fileDescriptor)
        val nl = ArrayList<Chunk>(snap.size)
        var off = 0L
        for (i in snap.indices) {
            val c = snap[i]
            nl.add(Chunk(off, blens[i], c.clen, c.nl, null, false))
            off += blens[i]
        }
        closeSource()
        chunks.clear()
        chunks.addAll(nl)
        cache.clear()
        fis = f2
        chan = f2.channel
        pfd = np
        srcKey = key
        gen++
        return true
    }

    private fun closeSource() {
        try { chan?.close() } catch (e: Exception) { }
        try { fis?.close() } catch (e: Exception) { }
        try { pfd?.close() } catch (e: Exception) { }
        chan = null
        fis = null
        pfd = null
    }

    @Synchronized
    fun close() {
        closeSource()
    }

    private fun flushBatch(batch: ArrayList<Chunk>) {
        appendIndexed(ArrayList(batch))
        batch.clear()
    }

    fun startIndex(size: Long, ch: FileChannel) {
        if (size <= 0L) return
        indexing = true
        indexPct = 0
        Thread {
            try {
                val buf = ByteBuffer.allocate(1 shl 20)
                val arr = buf.array()
                var pos = 0L
                var cOff = 0L
                var cBytes = 0
                var cChars = 0
                var cNl = 0
                val batch = ArrayList<Chunk>()
                while (pos < size) {
                    buf.clear()
                    val n = ch.read(buf, pos)
                    if (n <= 0) break
                    var i = 0
                    while (i < n) {
                        val b = arr[i].toInt() and 0xFF
                        if (cBytes >= CHUNK_BYTES && (b and 0xC0) != 0x80) {
                            batch.add(Chunk(cOff, cBytes, cChars, cNl, null, false))
                            cOff += cBytes
                            cBytes = 0
                            cChars = 0
                            cNl = 0
                            if (batch.size >= 64) flushBatch(batch)
                        }
                        if (b < 0x80) {
                            cChars++
                            if (b == 10) cNl++
                        } else if (b >= 0xF0) {
                            cChars += 2
                        } else if (b >= 0xC0) {
                            cChars++
                        }
                        cBytes++
                        i++
                    }
                    pos += n
                    indexPct = ((pos * 100L) / size).toInt()
                }
                if (cBytes > 0) batch.add(Chunk(cOff, cBytes, cChars, cNl, null, false))
                flushBatch(batch)
            } catch (e: Throwable) {
            }
            indexPct = 100
            indexing = false
        }.start()
    }

    companion object {
        fun fromString(s: String): Doc {
            val d = Doc()
            if (s.isNotEmpty()) d.replace(0L, 0L, s)
            return d
        }

        fun openFile(f: File): Doc {
            val size = f.length()
            if (size <= SMALL_FILE) return fromString(String(f.readBytes(), StandardCharsets.UTF_8))
            val fi = FileInputStream(f)
            val d = Doc()
            d.fis = fi
            d.chan = fi.channel
            d.startIndex(fi.channel.size(), fi.channel)
            return d
        }

        fun docKey(u: Uri): String {
            return try {
                (u.authority ?: "") + "|" + DocumentsContract.getDocumentId(u)
            } catch (e: Exception) {
                u.toString()
            }
        }

        fun openUri(ctx: Context, uri: Uri): Doc {
            val p = ctx.contentResolver.openFileDescriptor(uri, "r") ?: throw IOException("Cannot open file")
            val size = p.statSize
            if (size in 0L..SMALL_FILE) {
                val bytes = FileInputStream(p.fileDescriptor).use { it.readBytes() }
                p.close()
                val d = fromString(String(bytes, StandardCharsets.UTF_8))
                d.srcKey = docKey(uri)
                return d
            }
            val d = Doc()
            val f = FileInputStream(p.fileDescriptor)
            d.fis = f
            d.pfd = p
            d.chan = f.channel
            d.srcKey = docKey(uri)
            d.startIndex(f.channel.size(), f.channel)
            return d
        }
    }
}

const val DRAFT_MAX = 32000000L
const val MATCH = ViewGroup.LayoutParams.MATCH_PARENT
const val WRAPC = ViewGroup.LayoutParams.WRAP_CONTENT
val UI = Handler(Looper.getMainLooper())

class Seg {
    var start = 0L
    var end = 0L
    var next = 0L
}

class Tab(var filename: String, var fileUri: String?, var doc: Doc) {
    val id: Int = ++Store.idCounter
    var cur = 0L
    var anc = 0L
    var topPos = 0L
    var hx = 0
    var desiredCol = -1
    var dirty = false
    @Volatile var saving = false
    var compStart = -1L
    var compEnd = -1L
    var status: String? = null
    var draftGen = -1
    var draftName: String? = null
    val undoStack = ArrayList<Op>()
    val redoStack = ArrayList<Op>()
    var undoSize = 0L
    val views = ArrayList<BigEditor>()

    fun canEdit(): Boolean = !doc.indexing && !saving

    fun changed() {
        for (v in ArrayList(views)) v.docChanged()
    }

    fun edit(from: Long, to: Long, ins: String, kind: Int): Boolean {
        if (!canEdit()) return false
        val f = from.coerceIn(0L, doc.total)
        val t = to.coerceIn(f, doc.total)
        if (t == f && ins.isEmpty()) return true
        if (t - f > UNDO_MAX) {
            undoStack.clear()
            redoStack.clear()
            undoSize = 0L
            doc.replace(f, t, ins)
        } else {
            val del = doc.getText(f, t)
            doc.replace(f, t, ins)
            record(Op(f, del, ins, kind))
        }
        dirty = true
        return true
    }

    private fun record(op: Op) {
        redoStack.clear()
        val last: Op? = if (undoStack.isEmpty()) null else undoStack[undoStack.size - 1]
        if (last != null) {
            val lastEnd = last.pos + last.ins.length
            if (op.kind == 1 && last.kind == 1 && last.ins.length < 2000 &&
                op.pos >= last.pos && op.pos + op.del.length == lastEnd &&
                op.ins.indexOf('\n') < 0 && !last.ins.endsWith(" ") && !last.ins.endsWith("\n")) {
                val keep = (op.pos - last.pos).toInt()
                val oldLen = last.ins.length
                last.ins = last.ins.substring(0, keep) + op.ins
                undoSize += (last.ins.length - oldLen).toLong()
                return
            }
            if (op.kind == 2 && last.kind == 2 && op.pos + op.del.length == last.pos && last.del.length < 2000) {
                last.pos = op.pos
                last.del = op.del + last.del
                undoSize += op.del.length.toLong()
                return
            }
            if (op.kind == 3 && last.kind == 3 && op.pos == last.pos && last.del.length < 2000) {
                last.del = last.del + op.del
                undoSize += op.del.length.toLong()
                return
            }
        }
        undoStack.add(op)
        undoSize += (op.del.length + op.ins.length).toLong()
        while (undoSize > UNDO_TOTAL && undoStack.size > 1) {
            val o = undoStack.removeAt(0)
            undoSize -= (o.del.length + o.ins.length).toLong()
        }
    }

    fun undoStep(): Boolean {
        if (undoStack.isEmpty()) return false
        val op = undoStack.removeAt(undoStack.size - 1)
        undoSize -= (op.del.length + op.ins.length).toLong()
        doc.replace(op.pos, op.pos + op.ins.length, op.del)
        redoStack.add(op)
        cur = op.pos + op.del.length
        anc = cur
        compStart = -1L
        dirty = true
        return true
    }

    fun redoStep(): Boolean {
        if (redoStack.isEmpty()) return false
        val op = redoStack.removeAt(redoStack.size - 1)
        doc.replace(op.pos, op.pos + op.del.length, op.ins)
        undoStack.add(op)
        undoSize += (op.del.length + op.ins.length).toLong()
        cur = op.pos + op.ins.length
        anc = cur
        compStart = -1L
        dirty = true
        return true
    }
}

class PanelData(var folderUri: String, var folderName: String) {
    val id: Int = ++Store.idCounter
    val tabs = ArrayList<Tab>()
    var active = -1
    var ratio = 1.0

    fun activeTab(): Tab? = if (active >= 0 && active < tabs.size) tabs[active] else null
}

object Store {
    var idCounter = 0
    val panels = ArrayList<PanelData>()
    val views = ArrayList<PanelView>()
    var loaded = false
    var fresh = false
    var wrap = true
    var saveOnS = true
    var fontSp = 16f
    private val handler = Handler(Looper.getMainLooper())
    private var pending = false

    fun prefs(ctx: Context) = ctx.applicationContext.getSharedPreferences("tp", Context.MODE_PRIVATE)

    fun savePrefs(ctx: Context) {
        prefs(ctx).edit().putBoolean("wrap", wrap).putBoolean("saveOnS", saveOnS).putFloat("fontSp", fontSp).apply()
    }

    fun addTab(p: PanelData): Tab {
        val t = Tab("Untitled", null, Doc())
        p.tabs.add(t)
        p.active = p.tabs.size - 1
        return t
    }

    fun addPanel(): PanelData {
        val p = PanelData("", "")
        addTab(p)
        val n = panels.size
        panels.add(p)
        for (q in panels) q.ratio = 1.0 / (n + 1)
        normalize()
        return p
    }

    fun removePanel(p: PanelData) {
        panels.remove(p)
        normalize()
    }

    fun normalize() {
        var s = 0.0
        for (p in panels) s += p.ratio
        if (s <= 0.0) {
            for (p in panels) p.ratio = 1.0 / panels.size
        } else {
            for (p in panels) p.ratio = p.ratio / s
        }
    }

    fun panelById(id: Int): PanelData? {
        for (p in panels) if (p.id == id) return p
        return null
    }

    fun invalidateAll() {
        for (v in ArrayList(views)) v.editor.invalidate()
    }

    fun refreshPanel(id: Int) {
        for (v in ArrayList(views)) if (v.data.id == id) v.refreshAll()
    }

    fun touch(ctx: Context) {
        if (pending) return
        pending = true
        val app = ctx.applicationContext
        handler.postDelayed({
            pending = false
            persistAsync(app)
        }, 3000L)
    }

    fun persistAsync(ctx: Context) {
        val app = ctx.applicationContext
        Thread { persistNow(app) }.start()
    }

    fun ensureLoaded(ctx: Context) {
        if (loaded) return
        loaded = true
        val app = ctx.applicationContext
        val sp = prefs(app)
        wrap = sp.getBoolean("wrap", true)
        saveOnS = sp.getBoolean("saveOnS", true)
        fontSp = sp.getFloat("fontSp", 16f)
        val f = File(app.filesDir, MEM_FILE)
        if (f.exists()) {
            try {
                val root = JSONObject(String(f.readBytes(), StandardCharsets.UTF_8))
                val arr = root.optJSONArray("panels")
                if (arr != null) {
                    for (i in 0 until arr.length()) {
                        val po = arr.getJSONObject(i)
                        val p = PanelData(po.optString("folder_uri", ""), po.optString("folder_name", ""))
                        p.ratio = po.optDouble("ratio", 1.0)
                        val ta = po.optJSONArray("tabs")
                        if (ta != null) {
                            for (j in 0 until ta.length()) {
                                p.tabs.add(restoreTab(app, ta.getJSONObject(j)))
                            }
                        }
                        p.active = if (p.tabs.isEmpty()) -1 else po.optInt("active_tab", 0).coerceIn(0, p.tabs.size - 1)
                        panels.add(p)
                    }
                }
            } catch (e: Throwable) {
            }
        }
        if (panels.isEmpty()) {
            val p = PanelData("", "")
            addTab(p)
            panels.add(p)
            fresh = true
        }
        normalize()
    }

    private fun restoreTab(app: Context, to: JSONObject): Tab {
        val name = to.optString("filename", "Untitled")
        val furi = to.optString("file_uri", "")
        val draft = to.optString("draft", "")
        var doc: Doc? = null
        var dirty = false
        if (draft.isNotEmpty()) {
            val df = File(app.filesDir, draft)
            if (df.exists()) {
                try {
                    doc = Doc.openFile(df)
                    dirty = to.optBoolean("dirty", true)
                } catch (e: Throwable) {
                    doc = null
                }
            }
        }
        if (doc == null && furi.isNotEmpty()) {
            try {
                doc = Doc.openUri(app, Uri.parse(furi))
            } catch (e: Throwable) {
                doc = null
            }
        }
        val d: Doc = doc ?: Doc()
        val t = Tab(name, if (furi.isEmpty()) null else furi, d)
        t.dirty = dirty
        t.cur = to.optLong("cur", 0L)
        t.anc = t.cur
        t.topPos = to.optLong("top", 0L)
        if (draft.isNotEmpty()) t.draftName = draft
        return t
    }

    private fun writeDraft(app: Context, t: Tab): String? {
        val doc = t.doc
        val gen = doc.gen
        val old = t.draftName
        if (old != null && t.draftGen == gen && File(app.filesDir, old).exists()) return old
        val name = "draft_" + t.id + "_" + gen + "_" + System.currentTimeMillis() + ".txt"
        val f = File(app.filesDir, name)
        try {
            BufferedOutputStream(FileOutputStream(f), 1 shl 20).use { out ->
                val total = doc.total
                var p = 0L
                while (p < total) {
                    var e = minOf(total, p + 1000000L)
                    if (e < total && Character.isHighSurrogate(doc.charAtSafe(e - 1L))) e--
                    out.write(doc.getText(p, e).toByteArray(StandardCharsets.UTF_8))
                    p = e
                }
            }
        } catch (e: Throwable) {
            try { f.delete() } catch (x: Throwable) { }
            return null
        }
        t.draftName = name
        t.draftGen = gen
        return name
    }

    @Synchronized
    fun persistNow(app: Context) {
        try {
            val root = JSONObject()
            val arr = JSONArray()
            val keep = HashSet<String>()
            for (p in ArrayList(panels)) {
                val po = JSONObject()
                po.put("folder_uri", p.folderUri)
                po.put("folder_name", p.folderName)
                po.put("active_tab", p.active)
                po.put("ratio", p.ratio)
                val ta = JSONArray()
                for (t in ArrayList(p.tabs)) {
                    val to = JSONObject()
                    to.put("filename", t.filename)
                    to.put("file_uri", t.fileUri ?: "")
                    to.put("cur", t.cur)
                    to.put("top", t.topPos)
                    to.put("dirty", t.dirty)
                    if ((t.fileUri == null || t.dirty) && !t.doc.indexing && !t.saving && t.doc.total <= DRAFT_MAX) {
                        val dn = writeDraft(app, t)
                        if (dn != null) {
                            keep.add(dn)
                            to.put("draft", dn)
                        }
                    }
                    ta.put(to)
                }
                po.put("tabs", ta)
                arr.put(po)
            }
            root.put("panels", arr)
            val tmp = File(app.filesDir, MEM_FILE + ".tmp")
            tmp.writeBytes(root.toString().toByteArray(StandardCharsets.UTF_8))
            tmp.renameTo(File(app.filesDir, MEM_FILE))
            val list = app.filesDir.listFiles()
            if (list != null) {
                for (x in list) {
                    if (x.name.startsWith("draft_") && !keep.contains(x.name)) x.delete()
                }
            }
        } catch (e: Throwable) {
        }
    }
}

object Saver {
    private fun findChild(cr: android.content.ContentResolver, tree: Uri, treeDocId: String, name: String): Uri? {
        val childrenUri = DocumentsContract.buildChildDocumentsUriUsingTree(tree, treeDocId)
        val cols = arrayOf(DocumentsContract.Document.COLUMN_DOCUMENT_ID, DocumentsContract.Document.COLUMN_DISPLAY_NAME)
        val c = cr.query(childrenUri, cols, null, null, null) ?: return null
        try {
            while (c.moveToNext()) {
                val nm = c.getString(1)
                if (nm != null && nm == name) {
                    return DocumentsContract.buildDocumentUriUsingTree(tree, c.getString(0))
                }
            }
        } finally {
            c.close()
        }
        return null
    }

    private fun writeAll(doc: Doc, snap: ArrayList<Chunk>, blens: IntArray, out: OutputStream, progress: (Int) -> Unit) {
        val n = snap.size
        for (i in 0 until n) {
            val c = snap[i]
            val bytes = doc.chunkTextForSave(c).toByteArray(StandardCharsets.UTF_8)
            out.write(bytes)
            blens[i] = bytes.size
            if (i % 16 == 0) progress(((i.toLong() * 100L) / n).toInt())
        }
        out.flush()
    }

    // Returns the saved file's uri string. Runs on a background thread.
    fun saveTo(ctx: Context, folderUri: String, name: String, t: Tab, progress: (Int) -> Unit): String {
        val tree = Uri.parse(folderUri)
        val treeDocId = DocumentsContract.getTreeDocumentId(tree)
        val parent = DocumentsContract.buildDocumentUriUsingTree(tree, treeDocId)
        val cr = ctx.contentResolver
        var target: Uri? = findChild(cr, tree, treeDocId, name)
        if (target == null) {
            target = DocumentsContract.createDocument(cr, parent, "text/plain", name)
        }
        val tgt: Uri = target ?: throw IOException("Cannot create file")
        val doc = t.doc
        val snap = doc.snapshot()
        val blens = IntArray(snap.size)
        val hadBacking = doc.hasBacking()
        val sameSource = hadBacking && doc.srcKey != null && doc.srcKey == Doc.docKey(tgt)
        if (sameSource) {
            val tmp = File(ctx.cacheDir, "save_tmp_" + t.id + ".txt")
            BufferedOutputStream(FileOutputStream(tmp), 1 shl 20).use { out ->
                writeAll(doc, snap, blens, out, progress)
            }
            val os = cr.openOutputStream(tgt, "wt") ?: throw IOException("Cannot write file")
            try {
                FileInputStream(tmp).use { fin ->
                    val buf = ByteArray(1 shl 20)
                    while (true) {
                        val r = fin.read(buf)
                        if (r < 0) break
                        os.write(buf, 0, r)
                    }
                }
                os.flush()
            } finally {
                os.close()
            }
            tmp.delete()
        } else {
            val os = cr.openOutputStream(tgt, "wt") ?: throw IOException("Cannot write file")
            try {
                val bo = BufferedOutputStream(os, 1 shl 20)
                writeAll(doc, snap, blens, bo, progress)
                bo.flush()
            } finally {
                os.close()
            }
        }
        if (hadBacking) {
            try {
                val np = cr.openFileDescriptor(tgt, "r")
                if (np != null) {
                    val ok = doc.rebase(snap, blens, np, Doc.docKey(tgt))
                    if (!ok) np.close()
                }
            } catch (e: Throwable) {
            }
        }
        return tgt.toString()
    }
}

// ---------------------------------------------------------------------------
// BigEditor: custom editor view. Only the visible rows are ever read/drawn,
// so text of any size (KB..GB) scrolls and edits without freezing.
// ---------------------------------------------------------------------------
class BigEditor(ctx: Context) : View(ctx) {
    var tab: Tab? = null
    var statusCb: (() -> Unit)? = null
    var saveCb: (() -> Unit)? = null
    var host: Host? = null

    private val paint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val numPaint = Paint(Paint.ANTI_ALIAS_FLAG)
    private val fillP = Paint()
    private var appliedFont = -1f
    private var charW = 10f
    private var lineH = 20f
    private var ascentPx = 14f

    private val tmp = Seg()
    private val tmp2 = Seg()
    private val rowS = LongArray(260)
    private val rowE = LongArray(260)
    private val rowNx = LongArray(260)
    private val rowNum = LongArray(260)
    private var rowCount = 0

    private var gutterW = 0f
    private var textL = 0f
    private var availW = 100f
    private var viewH = 100f
    private var cols = 20
    private var fullRows = 10
    private var maxColSeen = 0
    private var accY = 0f
    private var imeBase = 0L
    private var ticking = false

    private var dragMode = 0
    private var downX = 0f
    private var downY = 0f
    private var lastX = 0f
    private var lastY = 0f
    private var moved = false
    private var selecting = false
    private var lastClickT = 0L
    private var lastClickPos = -10L
    private var vt: VelocityTracker? = null
    private val scroller = OverScroller(ctx)
    private var flingLastX = 0
    private var flingLastY = 0
    private val slop = ViewConfiguration.get(ctx).scaledTouchSlop

    private val scaleDetector = ScaleGestureDetector(ctx, object : ScaleGestureDetector.SimpleOnScaleGestureListener() {
        override fun onScale(detector: ScaleGestureDetector): Boolean {
            Store.fontSp = (Store.fontSp * detector.scaleFactor).coerceIn(8f, 48f)
            Store.invalidateAll()
            return true
        }

        override fun onScaleEnd(detector: ScaleGestureDetector) {
            Store.savePrefs(context)
        }
    })

    private val longRun = Runnable {
        val t = tab
        if (t != null && !moved && dragMode == 0) {
            performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
            selecting = true
            selectWord(hitPos(downX, downY))
            invalidate()
            statusCb?.invoke()
            notifyIme()
        }
    }

    private val tickRun = object : Runnable {
        override fun run() {
            val t = tab
            val still = t != null && t.doc.indexing
            statusCb?.invoke()
            invalidate()
            if (still) postDelayed(this, 300L) else ticking = false
        }
    }

    init {
        isFocusable = true
        isFocusableInTouchMode = true
    }

    // ----- binding -----
    fun bind(t: Tab?) {
        tab?.views?.remove(this)
        tab = t
        t?.views?.add(this)
        accY = 0f
        maxColSeen = 0
        rowCount = 0
        invalidate()
        if (t != null && t.doc.indexing) startTick()
        if (hasFocus()) {
            val imm = context.getSystemService(Context.INPUT_METHOD_SERVICE) as InputMethodManager
            imm.restartInput(this)
        }
    }

    override fun onAttachedToWindow() {
        super.onAttachedToWindow()
        val t = tab
        if (t != null && !t.views.contains(this)) t.views.add(this)
    }

    override fun onDetachedFromWindow() {
        super.onDetachedFromWindow()
        tab?.views?.remove(this)
        removeCallbacks(longRun)
        removeCallbacks(tickRun)
        ticking = false
    }

    fun docChanged() {
        invalidate()
        statusCb?.invoke()
        val t = tab
        if (t != null && t.doc.indexing) startTick()
    }

    private fun startTick() {
        if (!ticking) {
            ticking = true
            postDelayed(tickRun, 300L)
        }
    }

    // ----- metrics -----
    private fun applyFont() {
        if (appliedFont == Store.fontSp) return
        appliedFont = Store.fontSp
        val px = TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_SP, Store.fontSp, resources.displayMetrics)
        paint.typeface = Typeface.MONOSPACE
        paint.textSize = px
        paint.color = C_TXT
        numPaint.typeface = Typeface.MONOSPACE
        numPaint.textSize = px
        numPaint.color = C_NUM
        numPaint.textAlign = Paint.Align.RIGHT
        charW = paint.measureText("M")
        val fm = paint.fontMetrics
        lineH = (fm.descent - fm.ascent) + context.dpf(2f)
        ascentPx = -fm.ascent + context.dpf(1f)
    }

    private fun metrics() {
        applyFont()
        val t = tab
        val nl: Long = if (t == null) 0L else t.doc.totalNl
        val digits = maxOf(4, (nl + 1L).toString().length)
        gutterW = digits.toFloat() * charW + context.dpf(10f)
        textL = gutterW + context.dpf(8f)
        val sb = context.dpf(14f)
        val hb = if (Store.wrap) 0f else context.dpf(14f)
        availW = maxOf(charW, width.toFloat() - textL - sb)
        viewH = maxOf(lineH, height.toFloat() - hb)
        cols = maxOf(1, (availW / charW).toInt())
        fullRows = maxOf(1, (viewH / lineH).toInt())
    }

    // ----- row layout -----
    // Computes the visual row that starts at s. end = end of text on the row,
    // next = start of the following row.
    private fun segAt(doc: Doc, s: Long, out: Seg) {
        val total = doc.total
        if (s >= total) {
            out.start = s
            out.end = s
            out.next = s
            return
        }
        val le = doc.indexOfNl(s, s + LINE_CAP + 1L)
        val hasNl = le >= 0L
        val lineEnd: Long = if (hasNl) le else minOf(total, s + LINE_CAP)
        var end = lineEnd
        var next: Long = if (hasNl) lineEnd + 1L else lineEnd
        if (Store.wrap && lineEnd - s > cols.toLong()) {
            val c = cols
            val head = doc.getText(s, s + c.toLong())
            var cut = -1
            var i = head.length - 1
            val minIdx = c / 3
            while (i >= minIdx && i >= 0) {
                if (head[i] == ' ') {
                    cut = i + 1
                    break
                }
                i--
            }
            var e = if (cut > 0) cut else head.length
            if (e > 1 && e <= head.length && Character.isHighSurrogate(head[e - 1])) e--
            if (e < 1) e = 1
            end = s + e.toLong()
            next = end
        }
        out.start = s
        out.end = end
        out.next = next
    }

    // start of the visual row that contains position p
    private fun segContaining(doc: Doc, p: Long): Long {
        if (p <= 0L) return 0L
        val floor = maxOf(0L, p - MAX_BACK)
        val nl = doc.lastIndexOfNl(p, floor)
        var s: Long = if (nl >= 0L) nl + 1L else floor
        var guard = 0
        while (guard < 300000) {
            segAt(doc, s, tmp2)
            if (tmp2.next > p || tmp2.next <= s) return s
            s = tmp2.next
            guard++
        }
        return s
    }

    private fun prevStart(doc: Doc, a: Long): Long = if (a <= 0L) 0L else segContaining(doc, a - 1L)

    private fun rowStartOf(doc: Doc, pos: Long): Long = segContaining(doc, pos)

    // ----- drawing -----
    override fun onDraw(canvas: Canvas) {
        canvas.drawColor(C_ED)
        val t = tab ?: return
        metrics()
        val doc = t.doc
        val total = doc.total
        val wrap = Store.wrap
        val w = width.toFloat()
        val sbW = context.dpf(14f)
        val top: Long = if (t.topPos > total) total else if (t.topPos < 0L) 0L else t.topPos
        val maxRows = minOf(255, (viewH / lineH).toInt() + 2)

        var idx = doc.nlBefore(top)
        var s = top
        var n = 0
        while (n < maxRows) {
            segAt(doc, s, tmp)
            rowS[n] = tmp.start
            rowE[n] = tmp.end
            rowNx[n] = tmp.next
            rowNum[n] = if (tmp.start == 0L || doc.charAtSafe(tmp.start - 1L) == '\n') idx + 1L else 0L
            n++
            if (tmp.next > tmp.end) idx++
            if (tmp.start >= total) break
            if (tmp.next >= total && tmp.end == tmp.next) break
            if (tmp.next <= tmp.start) break
            s = tmp.next
        }
        rowCount = n

        val sel0 = minOf(t.cur, t.anc)
        val sel1 = maxOf(t.cur, t.anc)
        val hx = if (wrap) 0 else t.hx
        val c0 = if (wrap) 0 else (hx.toFloat() / charW).toInt()
        val visCols = (availW / charW).toInt() + 3
        canvas.save()
        canvas.clipRect(textL, 0f, w - sbW, viewH)
        for (r in 0 until n) {
            val y = r.toFloat() * lineH
            val rs = rowS[r]
            val re = rowE[r]
            val len = (re - rs).toInt()
            if (len > maxColSeen) maxColSeen = len
            if (sel1 > sel0 && sel1 > rs && sel0 <= re) {
                val a = maxOf(sel0, rs)
                val b = minOf(sel1, re)
                var cEnd = (b - rs).toInt()
                if (sel1 > re && rowNx[r] > re) cEnd++
                val x1 = textL + (a - rs).toFloat() * charW - hx.toFloat()
                val x2 = textL + cEnd.toFloat() * charW - hx.toFloat()
                fillP.color = C_SEL
                canvas.drawRect(x1, y, x2, y + lineH, fillP)
            }
            val a0 = rs + c0.toLong()
            val b0 = minOf(re, a0 + visCols.toLong())
            if (b0 > a0) {
                var tx = doc.getText(a0, b0)
                if (tx.indexOf('\t') >= 0 || tx.indexOf('\r') >= 0) tx = tx.replace('\t', ' ').replace('\r', ' ')
                canvas.drawText(tx, 0, tx.length, textL + c0.toFloat() * charW - hx.toFloat(), y + ascentPx, paint)
            }
        }
        canvas.restore()

        for (r in 0 until n) {
            val num = rowNum[r]
            if (num > 0L) canvas.drawText(num.toString(), gutterW - context.dpf(6f), r.toFloat() * lineH + ascentPx, numPaint)
        }

        var cr = -1
        for (r in 0 until n) {
            if (t.cur >= rowS[r] && t.cur <= rowE[r]) {
                if (t.cur == rowE[r] && rowNx[r] == rowE[r] && r + 1 < n) continue
                cr = r
                break
            }
        }
        if (cr >= 0) {
            val cx = textL + (t.cur - rowS[cr]).toFloat() * charW - hx.toFloat()
            if (cx >= textL - 2f && cx <= w - sbW) {
                fillP.color = C_GOLD
                canvas.drawRect(cx, cr.toFloat() * lineH, cx + context.dpf(2f), cr.toFloat() * lineH + lineH, fillP)
            }
        }

        fillP.color = C_STAT
        canvas.drawRect(w - sbW, 0f, w, viewH, fillP)
        val thumbH = context.dpf(40f)
        val frac = if (total > 0L) top.toFloat() / total.toFloat() else 0f
        val ty = frac.coerceIn(0f, 1f) * maxOf(0f, viewH - thumbH)
        fillP.color = if (dragMode == 1) C_GOLD else C_THUMB
        canvas.drawRect(w - sbW + 2f, ty, w - 2f, ty + thumbH, fillP)
        if (!wrap) {
            fillP.color = C_STAT
            canvas.drawRect(textL, viewH, w - sbW, height.toFloat(), fillP)
            val contentW = maxOf(maxColSeen.toFloat() * charW + charW * 2f, availW)
            val thumbW = maxOf(context.dpf(40f), availW / contentW * availW)
            val maxHx = contentW - availW
            val hf = if (maxHx > 0f) (hx.toFloat() / maxHx).coerceIn(0f, 1f) else 0f
            val tx0 = textL + hf * maxOf(0f, availW - thumbW)
            fillP.color = if (dragMode == 2) C_GOLD else C_THUMB
            canvas.drawRect(tx0, viewH + 2f, tx0 + thumbW, height.toFloat() - 2f, fillP)
        }
        if (doc.indexing) startTick()
    }

    // ----- scrolling -----
    fun scrollRows(n: Int) {
        val t = tab ?: return
        metrics()
        val doc = t.doc
        var top: Long = if (t.topPos > doc.total) doc.total else t.topPos
        if (n > 0) {
            var i = 0
            while (i < n) {
                segAt(doc, top, tmp)
                val nx = tmp.next
                if (nx <= top || nx > doc.total) break
                if (nx >= doc.total && tmp.end == nx) break
                top = nx
                i++
            }
        } else if (n < 0) {
            var i = 0
            while (i < -n && top > 0L) {
                top = prevStart(doc, top)
                i++
            }
        }
        t.topPos = top
        invalidate()
    }

    private fun scrollByPx(dx: Float, dy: Float) {
        val t = tab ?: return
        metrics()
        accY += dy
        val rows = (accY / lineH).toInt()
        if (rows != 0) {
            accY -= rows.toFloat() * lineH
            scrollRows(rows)
        }
        if (!Store.wrap && dx != 0f) {
            val maxHx = maxOf(0f, maxColSeen.toFloat() * charW + charW * 2f - availW)
            t.hx = (t.hx.toFloat() + dx).coerceIn(0f, maxHx).toInt()
            invalidate()
        }
    }

    private fun jumpV(y: Float) {
        val t = tab ?: return
        metrics()
        val thumbH = context.dpf(40f)
        val f = ((y - thumbH / 2f) / maxOf(1f, viewH - thumbH)).coerceIn(0f, 1f)
        val pos = (f.toDouble() * t.doc.total.toDouble()).toLong()
        t.topPos = t.doc.lineStartNear(pos)
        invalidate()
    }

    private fun jumpH(x: Float) {
        val t = tab ?: return
        metrics()
        val maxHx = maxOf(0f, maxColSeen.toFloat() * charW + charW * 2f - availW)
        val f = ((x - textL) / availW).coerceIn(0f, 1f)
        t.hx = (f * maxHx).toInt()
        invalidate()
    }

    override fun computeScroll() {
        if (scroller.computeScrollOffset()) {
            val cy = scroller.currY
            val cx = scroller.currX
            scrollByPx((cx - flingLastX).toFloat(), (cy - flingLastY).toFloat())
            flingLastX = cx
            flingLastY = cy
            postInvalidateOnAnimation()
        }
    }

    // ----- hit testing / selection -----
    private fun hitPos(x: Float, y: Float): Long {
        val t = tab ?: return 0L
        metrics()
        if (rowCount == 0) return 0L
        var r = (y / lineH).toInt()
        if (r < 0) r = 0
        if (r >= rowCount) r = rowCount - 1
        val rs = rowS[r]
        val re = rowE[r]
        val hx = if (Store.wrap) 0 else t.hx
        var col = Math.round((x - textL + hx.toFloat()) / charW)
        if (col < 0) col = 0
        val len = (re - rs).toInt()
        if (col > len) col = len
        return rs + col.toLong()
    }

    private fun isWordCh(c: Char): Boolean = Character.isLetterOrDigit(c) || c == '_'

    private fun selectWord(pos: Long) {
        val t = tab ?: return
        val doc = t.doc
        val a0 = maxOf(0L, pos - 200L)
        val s = doc.getText(a0, minOf(doc.total, pos + 200L))
        val p = (pos - a0).toInt().coerceIn(0, s.length)
        var a = p
        var b = p
        while (a > 0 && isWordCh(s[a - 1])) a--
        while (b < s.length && isWordCh(s[b])) b++
        if (a == b && b < s.length) b++
        t.anc = a0 + a.toLong()
        t.cur = a0 + b.toLong()
        t.compStart = -1L
    }

    private fun dragSelect(x: Float, y: Float) {
        val t = tab ?: return
        metrics()
        if (y < 0f) scrollRows(-1) else if (y > viewH) scrollRows(1)
        t.cur = hitPos(x, y.coerceIn(0f, maxOf(1f, viewH - 1f)))
        t.compStart = -1L
        t.desiredCol = -1
        invalidate()
        statusCb?.invoke()
        notifyIme()
    }

    override fun onTouchEvent(e: MotionEvent): Boolean {
        val t = tab ?: return true
        metrics()
        scaleDetector.onTouchEvent(e)
        if (scaleDetector.isInProgress) {
            removeCallbacks(longRun)
            moved = true
            return true
        }
        val x = e.x
        val y = e.y
        val mouse = e.getToolType(0) == MotionEvent.TOOL_TYPE_MOUSE
        val sbZone = context.dpf(14f) + context.dpf(8f)
        when (e.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                scroller.forceFinished(true)
                vt?.recycle()
                vt = VelocityTracker.obtain()
                vt?.addMovement(e)
                downX = x
                downY = y
                lastX = x
                lastY = y
                moved = false
                selecting = false
                dragMode = 0
                requestFocus()
                if (x > width.toFloat() - sbZone) {
                    dragMode = 1
                    jumpV(y)
                } else if (!Store.wrap && y > viewH) {
                    dragMode = 2
                    jumpH(x)
                } else if (mouse && (e.buttonState and MotionEvent.BUTTON_TERTIARY) != 0) {
                    dragMode = 3
                } else if (mouse) {
                    val pos = hitPos(x, y)
                    val now = e.eventTime
                    if (now - lastClickT < 350L && Math.abs(pos - lastClickPos) < 3L) {
                        selectWord(pos)
                        invalidate()
                        statusCb?.invoke()
                        notifyIme()
                    } else {
                        moveCaret(pos, false, false)
                        dragMode = 4
                    }
                    lastClickT = now
                    lastClickPos = pos
                } else {
                    postDelayed(longRun, ViewConfiguration.getLongPressTimeout().toLong())
                }
                invalidate()
            }
            MotionEvent.ACTION_MOVE -> {
                vt?.addMovement(e)
                if (dragMode == 1) {
                    jumpV(y)
                } else if (dragMode == 2) {
                    jumpH(x)
                } else if (dragMode == 3) {
                    scrollByPx(lastX - x, lastY - y)
                } else if (dragMode == 4) {
                    dragSelect(x, y)
                } else {
                    if (!moved) {
                        val dx = x - downX
                        val dy = y - downY
                        if (dx * dx + dy * dy > (slop * slop).toFloat()) {
                            moved = true
                            removeCallbacks(longRun)
                        }
                    }
                    if (selecting) dragSelect(x, y)
                    else if (moved) scrollByPx(lastX - x, lastY - y)
                }
                lastX = x
                lastY = y
            }
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                removeCallbacks(longRun)
                val up = e.actionMasked == MotionEvent.ACTION_UP
                if (dragMode == 0 && !selecting && !moved && up && !mouse) {
                    moveCaret(hitPos(x, y), false, false)
                    showKeyboard()
                } else if (dragMode == 0 && !selecting && moved && up) {
                    val v = vt
                    if (v != null) {
                        v.computeCurrentVelocity(1000)
                        val vx = if (Store.wrap) 0 else (-v.xVelocity).toInt()
                        val vy = (-v.yVelocity).toInt()
                        if (Math.abs(vx) > 200 || Math.abs(vy) > 200) {
                            flingLastX = 0
                            flingLastY = 0
                            scroller.fling(0, 0, vx, vy, -100000000, 100000000, -100000000, 100000000)
                            postInvalidateOnAnimation()
                        }
                    }
                }
                vt?.recycle()
                vt = null
                dragMode = 0
                selecting = false
                invalidate()
            }
        }
        return true
    }

    override fun onGenericMotionEvent(e: MotionEvent): Boolean {
        if (e.actionMasked == MotionEvent.ACTION_SCROLL && (e.source and InputDevice.SOURCE_CLASS_POINTER) != 0) {
            metrics()
            val vs = e.getAxisValue(MotionEvent.AXIS_VSCROLL)
            val hs = e.getAxisValue(MotionEvent.AXIS_HSCROLL)
            val ctrl = (e.metaState and KeyEvent.META_CTRL_ON) != 0
            val shift = (e.metaState and KeyEvent.META_SHIFT_ON) != 0
            if (ctrl) {
                Store.fontSp = (Store.fontSp + (if (vs > 0f) 1f else -1f)).coerceIn(8f, 48f)
                Store.savePrefs(context)
                Store.invalidateAll()
                return true
            }
            if (shift) {
                scrollByPx(-vs * charW * 6f, 0f)
                return true
            }
            if (hs != 0f) scrollByPx(hs * charW * 6f, 0f)
            if (vs != 0f) {
                var rws = Math.round(-vs * 3f)
                if (rws == 0) rws = if (vs > 0f) -1 else 1
                scrollRows(rws)
            }
            return true
        }
        return super.onGenericMotionEvent(e)
    }

    // ----- caret movement -----
    private fun stepLeft(doc: Doc, pos: Long): Long {
        if (pos <= 0L) return 0L
        if (pos >= 2L && Character.isLowSurrogate(doc.charAtSafe(pos - 1L)) && Character.isHighSurrogate(doc.charAtSafe(pos - 2L))) return pos - 2L
        return pos - 1L
    }

    private fun stepRight(doc: Doc, pos: Long): Long {
        if (pos >= doc.total) return doc.total
        if (Character.isHighSurrogate(doc.charAtSafe(pos)) && pos + 1L < doc.total) return pos + 2L
        return pos + 1L
    }

    private fun wordLeft(doc: Doc, pos: Long): Long {
        val a = maxOf(0L, pos - 300L)
        val s = doc.getText(a, pos)
        var i = s.length
        while (i > 0 && !isWordCh(s[i - 1])) i--
        while (i > 0 && isWordCh(s[i - 1])) i--
        return a + i.toLong()
    }

    private fun wordRight(doc: Doc, pos: Long): Long {
        val s = doc.getText(pos, minOf(doc.total, pos + 300L))
        var i = 0
        while (i < s.length && !isWordCh(s[i])) i++
        while (i < s.length && isWordCh(s[i])) i++
        return pos + i.toLong()
    }

    private fun moveCaret(p0: Long, extend: Boolean, keepCol: Boolean) {
        val t = tab ?: return
        val p = p0.coerceIn(0L, t.doc.total)
        t.cur = p
        if (!extend) t.anc = p
        if (!keepCol) t.desiredCol = -1
        t.compStart = -1L
        t.status = null
        metrics()
        ensureVisible()
        invalidate()
        statusCb?.invoke()
        notifyIme()
    }

    private fun ensureVisible() {
        val t = tab ?: return
        val doc = t.doc
        val cur = t.cur
        var r = -1
        for (i in 0 until rowCount) {
            if (cur >= rowS[i] && cur <= rowE[i]) {
                r = i
                break
            }
        }
        val rs = rowStartOf(doc, cur)
        if (r < 0 || r >= fullRows) {
            if (rowCount == 0 || cur < rowS[0]) {
                t.topPos = rs
            } else {
                var s = rs
                var i = 0
                while (i < fullRows - 1 && s > 0L) {
                    s = prevStart(doc, s)
                    i++
                }
                t.topPos = s
            }
        }
        if (!Store.wrap) {
            val x = (cur - rs).toFloat() * charW
            if (x < t.hx.toFloat()) {
                t.hx = maxOf(0f, x - charW * 4f).toInt()
            } else if (x + charW > t.hx.toFloat() + availW) {
                t.hx = (x + charW - availW + charW * 4f).toInt()
            }
        } else {
            t.hx = 0
        }
    }

    private fun moveVertical(rows: Int, extend: Boolean) {
        val t = tab ?: return
        metrics()
        val doc = t.doc
        val rs = rowStartOf(doc, t.cur)
        if (t.desiredCol < 0) t.desiredCol = (t.cur - rs).toInt()
        var s = rs
        var toEnd = false
        if (rows < 0) {
            var i = 0
            while (i < -rows) {
                if (s <= 0L) break
                s = prevStart(doc, s)
                i++
            }
        } else {
            var i = 0
            while (i < rows) {
                segAt(doc, s, tmp)
                val nx = tmp.next
                if (nx <= s || nx > doc.total || (nx >= doc.total && tmp.end == nx)) {
                    toEnd = true
                    break
                }
                s = nx
                i++
            }
        }
        segAt(doc, s, tmp)
        val len = (tmp.end - s).toInt()
        val pos: Long = if (toEnd) tmp.end else s + minOf(t.desiredCol, len).toLong()
        moveCaret(pos, extend, true)
    }

    // ----- editing -----
    private fun guard(t: Tab): Boolean {
        if (t.doc.indexing) {
            host?.toast("Still indexing - editing unlocks when done")
            return false
        }
        if (t.saving) {
            host?.toast("Saving...")
            return false
        }
        return true
    }

    private fun afterEdit() {
        val t = tab ?: return
        t.desiredCol = -1
        t.status = null
        metrics()
        ensureVisible()
        t.changed()
        notifyIme()
        Store.touch(context)
    }

    fun insertText(s: String, kind: Int) {
        val t = tab ?: return
        if (!guard(t)) return
        val a = minOf(t.cur, t.anc)
        val b = maxOf(t.cur, t.anc)
        if (!t.edit(a, b, s, kind)) return
        t.cur = a + s.length.toLong()
        t.anc = t.cur
        t.compStart = -1L
        afterEdit()
    }

    private fun deleteRange(a: Long, b: Long, kind: Int) {
        val t = tab ?: return
        if (a >= b) return
        if (!guard(t)) return
        if (!t.edit(a, b, "", kind)) return
        t.cur = a
        t.anc = a
        t.compStart = -1L
        afterEdit()
    }

    private fun cm(): ClipboardManager = context.getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager

    fun copySel(): Boolean {
        val t = tab ?: return false
        val a = minOf(t.cur, t.anc)
        val b = maxOf(t.cur, t.anc)
        if (a == b) return false
        if (b - a > 2000000L) {
            host?.toast("Selection too large to copy (max 2,000,000 characters)")
            return false
        }
        cm().setPrimaryClip(ClipData.newPlainText("text", t.doc.getText(a, b)))
        return true
    }

    fun cutSel() {
        val t = tab ?: return
        if (copySel()) deleteRange(minOf(t.cur, t.anc), maxOf(t.cur, t.anc), 4)
    }

    fun paste() {
        val clip = cm().primaryClip ?: return
        if (clip.itemCount == 0) return
        val s = clip.getItemAt(0).coerceToText(context)?.toString() ?: return
        if (s.isNotEmpty()) insertText(s, 4)
    }

    fun selectAll() {
        val t = tab ?: return
        t.anc = 0L
        moveCaret(t.doc.total, true, false)
    }

    fun undoCmd() {
        val t = tab ?: return
        if (!guard(t)) return
        if (t.undoStep()) afterEdit()
    }

    fun redoCmd() {
        val t = tab ?: return
        if (!guard(t)) return
        if (t.redoStep()) afterEdit()
    }

    fun goTo(input: String) {
        val t = tab ?: return
        val doc = t.doc
        val s = input.trim()
        if (s.isEmpty()) return
        val pos: Long
        if (s.endsWith("%")) {
            val f = s.substring(0, s.length - 1).trim().toDoubleOrNull() ?: return
            val p = (f.coerceIn(0.0, 100.0) / 100.0 * doc.total.toDouble()).toLong()
            pos = doc.lineStartNear(p)
        } else {
            val n = s.toLongOrNull() ?: return
            pos = doc.posOfLine(n - 1L)
        }
        t.topPos = pos
        t.cur = pos
        t.anc = pos
        t.compStart = -1L
        t.status = null
        invalidate()
        statusCb?.invoke()
        notifyIme()
    }

    fun posInfo(): String {
        val t = tab ?: return ""
        val ln = t.doc.nlBefore(t.cur) + 1L
        val col = t.cur - t.doc.lineStartNear(t.cur) + 1L
        return "Ln $ln, Col $col"
    }

    fun showKeyboard() {
        requestFocus()
        val imm = context.getSystemService(Context.INPUT_METHOD_SERVICE) as InputMethodManager
        imm.showSoftInput(this, InputMethodManager.SHOW_IMPLICIT)
    }

    // ----- keyboard -----
    override fun onKeyDown(keyCode: Int, event: KeyEvent): Boolean {
        if (handleKey(keyCode, event)) return true
        return super.onKeyDown(keyCode, event)
    }

    private fun handleKey(keyCode: Int, e: KeyEvent): Boolean {
        val t = tab ?: return false
        val ctrl = e.isCtrlPressed
        val shift = e.isShiftPressed
        val alt = e.isAltPressed
        metrics()
        val doc = t.doc
        val hasSel = t.cur != t.anc
        val selA = minOf(t.cur, t.anc)
        val selB = maxOf(t.cur, t.anc)

        if (ctrl && !alt) {
            when (keyCode) {
                KeyEvent.KEYCODE_A -> { selectAll(); return true }
                KeyEvent.KEYCODE_C -> { copySel(); return true }
                KeyEvent.KEYCODE_X -> { cutSel(); return true }
                KeyEvent.KEYCODE_V -> { paste(); return true }
                KeyEvent.KEYCODE_Z -> {
                    if (shift) redoCmd() else undoCmd()
                    return true
                }
                KeyEvent.KEYCODE_Y -> { redoCmd(); return true }
            }
        }
        when (keyCode) {
            KeyEvent.KEYCODE_DPAD_LEFT -> {
                if (hasSel && !shift) moveCaret(selA, false, false)
                else moveCaret(if (ctrl) wordLeft(doc, t.cur) else stepLeft(doc, t.cur), shift, false)
                return true
            }
            KeyEvent.KEYCODE_DPAD_RIGHT -> {
                if (hasSel && !shift) moveCaret(selB, false, false)
                else moveCaret(if (ctrl) wordRight(doc, t.cur) else stepRight(doc, t.cur), shift, false)
                return true
            }
            KeyEvent.KEYCODE_DPAD_UP -> { moveVertical(-1, shift); return true }
            KeyEvent.KEYCODE_DPAD_DOWN -> { moveVertical(1, shift); return true }
            KeyEvent.KEYCODE_PAGE_UP -> { moveVertical(-fullRows, shift); return true }
            KeyEvent.KEYCODE_PAGE_DOWN -> { moveVertical(fullRows, shift); return true }
            KeyEvent.KEYCODE_MOVE_HOME -> {
                moveCaret(if (ctrl) 0L else rowStartOf(doc, t.cur), shift, false)
                return true
            }
            KeyEvent.KEYCODE_MOVE_END -> {
                if (ctrl) {
                    moveCaret(doc.total, shift, false)
                } else {
                    val rs = rowStartOf(doc, t.cur)
                    segAt(doc, rs, tmp)
                    var p = tmp.end
                    if (tmp.next == tmp.end && tmp.end < doc.total && p > rs) p--
                    moveCaret(p, shift, false)
                }
                return true
            }
            KeyEvent.KEYCODE_DEL -> {
                if (hasSel) deleteRange(selA, selB, 4)
                else if (t.cur > 0L) deleteRange(stepLeft(doc, t.cur), t.cur, 2)
                return true
            }
            KeyEvent.KEYCODE_FORWARD_DEL -> {
                if (hasSel) deleteRange(selA, selB, 4)
                else if (t.cur < doc.total) deleteRange(t.cur, stepRight(doc, t.cur), 3)
                return true
            }
            KeyEvent.KEYCODE_ENTER, KeyEvent.KEYCODE_NUMPAD_ENTER -> {
                insertText("\n", 1)
                return true
            }
            KeyEvent.KEYCODE_TAB -> {
                if (!shift) insertText("\t", 1)
                return true
            }
            KeyEvent.KEYCODE_S -> {
                if (!ctrl && !shift && !alt && Store.saveOnS) {
                    saveCb?.invoke()
                    return true
                }
            }
        }
        if (!ctrl && !alt && !e.isMetaPressed) {
            val uc = e.unicodeChar
            if (uc != 0 && (uc and KeyCharacterMap.COMBINING_ACCENT) == 0 && uc >= 32 && uc != 127) {
                insertText(String(Character.toChars(uc)), 1)
                return true
            }
        }
        return false
    }

    // ----- IME (soft keyboard) -----
    override fun onCheckIsTextEditor(): Boolean = true

    override fun onCreateInputConnection(outAttrs: EditorInfo): InputConnection {
        outAttrs.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_MULTI_LINE or InputType.TYPE_TEXT_FLAG_NO_SUGGESTIONS
        outAttrs.imeOptions = EditorInfo.IME_FLAG_NO_FULLSCREEN or EditorInfo.IME_FLAG_NO_EXTRACT_UI
        val t = tab
        if (t != null) {
            imeBase = maxOf(0L, t.cur - 3000L)
            outAttrs.initialSelStart = (t.cur - imeBase).coerceIn(0L, 2000000000L).toInt()
            outAttrs.initialSelEnd = (t.anc - imeBase).coerceIn(0L, 2000000000L).toInt()
        }
        return EditorIC()
    }

    private fun notifyIme() {
        val t = tab ?: return
        if (!hasFocus()) return
        val imm = context.getSystemService(Context.INPUT_METHOD_SERVICE) as InputMethodManager
        val c = t.cur
        if (c < imeBase || c - imeBase > 6000L) {
            imm.restartInput(this)
            return
        }
        val comp = t.compStart >= 0L
        val cs = if (comp) (t.compStart - imeBase).coerceIn(0L, 2000000000L).toInt() else -1
        val ce = if (comp) (t.compEnd - imeBase).coerceIn(0L, 2000000000L).toInt() else -1
        imm.updateSelection(this, (c - imeBase).toInt(), (t.anc - imeBase).coerceIn(0L, 2000000000L).toInt(), cs, ce)
    }

    private fun composeText(text: String, commit: Boolean): Boolean {
        val t = tab ?: return true
        if (!guard(t)) return true
        val a: Long
        val b: Long
        if (t.compStart >= 0L) {
            a = t.compStart
            b = t.compEnd
        } else {
            a = minOf(t.cur, t.anc)
            b = maxOf(t.cur, t.anc)
        }
        if (!t.edit(a, b, text, 1)) return true
        t.cur = a + text.length.toLong()
        t.anc = t.cur
        if (commit || text.isEmpty()) {
            t.compStart = -1L
        } else {
            t.compStart = a
            t.compEnd = a + text.length.toLong()
        }
        afterEdit()
        return true
    }

    private inner class EditorIC : BaseInputConnection(this@BigEditor, true) {
        override fun getTextBeforeCursor(n: Int, flags: Int): CharSequence {
            val t = tab ?: return ""
            val a = minOf(t.cur, t.anc)
            return t.doc.getText(maxOf(0L, a - n.toLong()), a)
        }

        override fun getTextAfterCursor(n: Int, flags: Int): CharSequence {
            val t = tab ?: return ""
            val b = maxOf(t.cur, t.anc)
            return t.doc.getText(b, minOf(t.doc.total, b + n.toLong()))
        }

        override fun getSelectedText(flags: Int): CharSequence? {
            val t = tab ?: return null
            val a = minOf(t.cur, t.anc)
            val b = maxOf(t.cur, t.anc)
            if (a == b || b - a > 100000L) return null
            return t.doc.getText(a, b)
        }

        override fun commitText(text: CharSequence?, newCursorPosition: Int): Boolean {
            return composeText(text?.toString() ?: "", true)
        }

        override fun setComposingText(text: CharSequence?, newCursorPosition: Int): Boolean {
            return composeText(text?.toString() ?: "", false)
        }

        override fun setComposingRegion(start: Int, end: Int): Boolean {
            val t = tab ?: return true
            val a = (imeBase + minOf(start, end).toLong()).coerceIn(0L, t.doc.total)
            val b = (imeBase + maxOf(start, end).toLong()).coerceIn(0L, t.doc.total)
            if (a == b) {
                t.compStart = -1L
            } else {
                t.compStart = a
                t.compEnd = b
            }
            return true
        }

        override fun finishComposingText(): Boolean {
            val t = tab
            if (t != null) t.compStart = -1L
            return true
        }

        override fun deleteSurroundingText(beforeLength: Int, afterLength: Int): Boolean {
            val t = tab ?: return true
            if (!guard(t)) return true
            if (t.cur != t.anc) {
                deleteRange(minOf(t.cur, t.anc), maxOf(t.cur, t.anc), 4)
                return true
            }
            val a = maxOf(0L, t.cur - beforeLength.toLong())
            val b = minOf(t.doc.total, t.cur + afterLength.toLong())
            deleteRange(a, b, if (afterLength == 0) 2 else 3)
            return true
        }

        override fun sendKeyEvent(event: KeyEvent?): Boolean {
            if (event != null && event.action == KeyEvent.ACTION_DOWN) handleKey(event.keyCode, event)
            return true
        }

        override fun performEditorAction(editorAction: Int): Boolean {
            insertText("\n", 1)
            return true
        }

        override fun setSelection(start: Int, end: Int): Boolean {
            val t = tab ?: return true
            val a = (imeBase + start.toLong()).coerceIn(0L, t.doc.total)
            val b = (imeBase + end.toLong()).coerceIn(0L, t.doc.total)
            t.anc = a
            moveCaret(b, true, false)
            return true
        }

        override fun beginBatchEdit(): Boolean = true

        override fun endBatchEdit(): Boolean = true

        override fun getExtractedText(request: ExtractedTextRequest?, flags: Int): ExtractedText? = null
    }
}

const val MIN_RATIO = 0.10

fun fmtCount(n: Long): String {
    return if (n >= 1000000000L) String.format("%.2fG", n.toDouble() / 1e9)
    else if (n >= 1000000L) String.format("%.2fM", n.toDouble() / 1e6)
    else if (n >= 1000L) String.format("%.1fK", n.toDouble() / 1e3)
    else n.toString()
}

fun askText(host: Host, title: String, msg: String, initial: String, okLabel: String, onOk: (String) -> Unit) {
    val ctx = host.dialogContext()
    val et = EditText(ctx)
    et.setSingleLine(true)
    et.setText(initial)
    et.setSelection(et.text.length)
    val d = AlertDialog.Builder(ctx)
        .setTitle(title)
        .setMessage(msg)
        .setView(et)
        .setPositiveButton(okLabel) { _, _ -> onOk(et.text.toString()) }
        .setNegativeButton("Cancel", null)
        .create()
    d.window?.setSoftInputMode(WindowManager.LayoutParams.SOFT_INPUT_STATE_VISIBLE)
    host.showDialog(d)
}

fun confirmDlg(host: Host, title: String, msg: String, onYes: () -> Unit) {
    val d = AlertDialog.Builder(host.dialogContext())
        .setTitle(title)
        .setMessage(msg)
        .setPositiveButton("Yes") { _, _ -> onYes() }
        .setNegativeButton("No", null)
        .create()
    host.showDialog(d)
}

// ---------------------------------------------------------------------------
// PanelView: one panel = one folder + header buttons + tab bar + editor
// ---------------------------------------------------------------------------
class PanelView(ctx: Context, val host: Host, val data: PanelData, val overlay: Boolean) : LinearLayout(ctx) {
    private val folderLabel = TextView(ctx)
    private val tabRow = LinearLayout(ctx)
    private val status = TextView(ctx)
    val editor = BigEditor(ctx)

    init {
        orientation = LinearLayout.VERTICAL
        setBackgroundColor(C_BG)

        val head = LinearLayout(ctx)
        head.orientation = LinearLayout.VERTICAL
        head.setBackgroundColor(C_HEAD)
        folderLabel.setTextColor(C_DIM)
        folderLabel.textSize = 11f
        folderLabel.typeface = Typeface.MONOSPACE
        folderLabel.setSingleLine(true)
        folderLabel.ellipsize = TextUtils.TruncateAt.START
        folderLabel.setPadding(ctx.dp(8), ctx.dp(4), ctx.dp(8), ctx.dp(1))
        head.addView(folderLabel, LinearLayout.LayoutParams(MATCH, WRAPC))

        val bs = HorizontalScrollView(ctx)
        bs.isHorizontalScrollBarEnabled = false
        val row = LinearLayout(ctx)
        row.orientation = LinearLayout.HORIZONTAL
        row.setPadding(ctx.dp(3), 0, ctx.dp(3), 0)
        fun addB(text: String, bg: Int, fg: Int, act: () -> Unit) {
            val b = mkBtn(ctx, text, bg, fg, 12f, act)
            val lp = LinearLayout.LayoutParams(WRAPC, WRAPC)
            lp.setMargins(ctx.dp(2), ctx.dp(2), ctx.dp(2), ctx.dp(4))
            row.addView(b, lp)
        }
        addB("💾 Save", C_BTN, C_GOLD) { save() }
        addB("↩ Undo", C_UR, C_TXT) { editor.undoCmd() }
        addB("↪ Redo", C_UR, C_TXT) { editor.redoCmd() }
        addB("Copy", C_BTN, C_TXT) { editor.copySel() }
        addB("Cut", C_BTN, C_TXT) { editor.cutSel() }
        addB("Paste", C_BTN, C_TXT) { editor.paste() }
        addB("All", C_BTN, C_TXT) { editor.selectAll() }
        addB("Go", C_BTN, C_TXT) {
            askText(host, "Go to", "Line number, or percent of the file (e.g. 50%)", "", "Go") { editor.goTo(it) }
        }
        addB("＋", C_BTN, C_TXT) { newTab() }
        addB("✕ Tab", C_BTN, C_TXT) { closeTab() }
        addB("📁", C_BTN, C_TXT) { host.pickFolder(data.id) }
        addB("📄 Open", C_BTN, C_TXT) { host.pickOpen(data.id) }
        if (!overlay) {
            addB("📌 Top", C_BTN, C_GOLD) { host.toggleTop(data.id) }
            addB("✖ Panel", C_RMBG, C_RMFG) { removeThisPanel() }
        }
        bs.addView(row, FrameLayout.LayoutParams(WRAPC, WRAPC))
        head.addView(bs, LinearLayout.LayoutParams(MATCH, WRAPC))
        addView(head, LinearLayout.LayoutParams(MATCH, WRAPC))

        val ts = HorizontalScrollView(ctx)
        ts.isHorizontalScrollBarEnabled = false
        ts.setBackgroundColor(C_ED)
        tabRow.orientation = LinearLayout.HORIZONTAL
        ts.addView(tabRow, FrameLayout.LayoutParams(WRAPC, WRAPC))
        addView(ts, LinearLayout.LayoutParams(MATCH, WRAPC))

        editor.host = host
        editor.statusCb = { updateStatus() }
        editor.saveCb = { save() }
        addView(editor, LinearLayout.LayoutParams(MATCH, 0, 1f))

        status.setTextColor(C_DIM)
        status.setBackgroundColor(C_STAT)
        status.textSize = 10f
        status.typeface = Typeface.MONOSPACE
        status.setSingleLine(true)
        status.ellipsize = TextUtils.TruncateAt.END
        status.setPadding(ctx.dp(6), ctx.dp(3), ctx.dp(6), ctx.dp(3))
        addView(status, LinearLayout.LayoutParams(MATCH, WRAPC))

        refreshAll()
    }

    override fun onAttachedToWindow() {
        super.onAttachedToWindow()
        if (!Store.views.contains(this)) Store.views.add(this)
    }

    override fun onDetachedFromWindow() {
        super.onDetachedFromWindow()
        Store.views.remove(this)
    }

    fun refreshAll() {
        refreshFolder()
        renderTabs()
        editor.bind(data.activeTab())
        updateStatus()
    }

    private fun refreshFolder() {
        if (data.folderUri.isNotEmpty()) {
            var s = data.folderName
            if (s.length > 38) s = "…" + s.substring(s.length - 36)
            folderLabel.text = "📂 " + s
            folderLabel.setTextColor(C_FOLDER)
        } else {
            folderLabel.text = "📂 No folder"
            folderLabel.setTextColor(C_DIM)
        }
    }

    private fun renderTabs() {
        tabRow.removeAllViews()
        for (i in 0 until data.tabs.size) {
            val t = data.tabs[i]
            val active = i == data.active
            val nm = if (t.filename.length <= 14) t.filename else t.filename.substring(0, 12) + "…"
            val label = if (t.dirty) nm + " •" else nm
            val b = mkBtn(context, label, if (active) C_SEL else C_STAT, if (active) C_GOLD else C_FOLDER, 12f) { switchTab(i) }
            val lp = LinearLayout.LayoutParams(WRAPC, WRAPC)
            lp.setMargins(context.dp(1), context.dp(2), context.dp(1), context.dp(2))
            tabRow.addView(b, lp)
        }
    }

    fun updateStatus() {
        val t = data.activeTab()
        if (t == null) {
            status.text = "No tab - press ＋ to create one"
            return
        }
        val m = t.status
        if (m != null) {
            status.text = m
            return
        }
        val sb = StringBuilder()
        sb.append(editor.posInfo())
        sb.append("  |  ").append(fmtCount(t.doc.total)).append(" chars")
        if (t.doc.indexing) sb.append("  |  Indexing ").append(t.doc.indexPct).append("%")
        if (Store.saveOnS) sb.append("  |  S = save") else sb.append("  |  Save button")
        sb.append("  |  Ctrl+Z / Ctrl+Y  |  ")
        sb.append(if (data.folderUri.isEmpty()) "No folder" else data.folderName)
        status.text = sb.toString()
    }

    private fun switchTab(i: Int) {
        data.active = i
        refreshAll()
        editor.requestFocus()
        Store.touch(context)
    }

    private fun newTab() {
        Store.addTab(data)
        refreshAll()
        editor.requestFocus()
        Store.touch(context)
    }

    private fun closeTab() {
        val t = data.activeTab() ?: return
        val doIt: () -> Unit = {
            val idx = data.active
            if (idx >= 0 && idx < data.tabs.size) data.tabs.removeAt(idx)
            t.doc.close()
            data.active = if (data.tabs.isEmpty()) -1 else minOf(idx, data.tabs.size - 1)
            refreshAll()
            Store.touch(context)
        }
        if (t.dirty && t.doc.total > 0L) {
            confirmDlg(host, "Close Tab", "This tab has unsaved changes. Close it anyway?") { doIt() }
        } else {
            doIt()
        }
    }

    private fun removeThisPanel() {
        confirmDlg(host, "Remove Panel", "Remove this panel? (Files won't be deleted)") {
            if (Store.panels.size <= 1) {
                host.toast("You need at least one panel.")
            } else {
                Store.removePanel(data)
                host.panelsChanged()
                Store.touch(context)
            }
        }
    }

    fun save() {
        val t = data.activeTab()
        if (t == null) {
            host.toast("Open or create a tab first.")
            return
        }
        if (data.folderUri.isEmpty()) {
            host.toast("Please choose a folder first.")
            host.pickFolder(data.id)
            return
        }
        if (t.doc.indexing) {
            host.toast("Still indexing - please wait")
            return
        }
        if (t.saving) return
        askText(host, "Save File", "Enter file name (without .txt):", if (t.filename != "Untitled") t.filename else "", "Save") { nm0 ->
            var nm = nm0.trim()
            if (nm.isNotEmpty()) {
                if (!nm.endsWith(".txt")) nm += ".txt"
                doSave(t, nm)
            }
        }
    }

    private fun doSave(t: Tab, name: String) {
        t.saving = true
        t.status = "Saving..."
        updateStatus()
        val app = context.applicationContext
        val folder = data.folderUri
        val pid = data.id
        Thread {
            try {
                val uri = Saver.saveTo(app, folder, name, t) { pct ->
                    UI.post {
                        t.status = "Saving " + pct + "%"
                        t.changed()
                    }
                }
                UI.post {
                    t.filename = name
                    t.fileUri = uri
                    t.dirty = false
                    t.saving = false
                    t.status = "Saved: " + name
                    Store.refreshPanel(pid)
                    Store.touch(app)
                }
            } catch (e: Throwable) {
                val msg = e.message ?: e.toString()
                UI.post {
                    t.saving = false
                    t.status = null
                    host.toast("Save Error: " + msg)
                    t.changed()
                }
            }
        }.start()
    }
}

// ---------------------------------------------------------------------------
// Side-by-side panels with draggable dividers (proportional, min 10% each)
// ---------------------------------------------------------------------------
class DividerView(ctx: Context, val idx: Int, val pc: PanelsContainer) : View(ctx) {
    private val p = Paint(Paint.ANTI_ALIAS_FLAG)
    private var hot = false

    override fun onDraw(canvas: Canvas) {
        canvas.drawColor(if (hot) C_DIVH else C_DIV)
        p.color = if (hot) C_GOLD else C_DIM
        val cx = width.toFloat() / 2f
        val cy = height.toFloat() / 2f
        for (k in -1..1) canvas.drawCircle(cx, cy + k.toFloat() * context.dpf(8f), context.dpf(1.6f), p)
    }

    override fun onTouchEvent(e: MotionEvent): Boolean {
        when (e.actionMasked) {
            MotionEvent.ACTION_DOWN -> {
                hot = true
                parent.requestDisallowInterceptTouchEvent(true)
                pc.dragStart(idx, e.rawX)
                invalidate()
            }
            MotionEvent.ACTION_MOVE -> pc.dragMove(e.rawX)
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                hot = false
                pc.dragEnd()
                invalidate()
            }
        }
        return true
    }

    override fun onResolvePointerIcon(event: MotionEvent, pointerIndex: Int): PointerIcon? {
        return PointerIcon.getSystemIcon(context, PointerIcon.TYPE_HORIZONTAL_DOUBLE_ARROW)
    }
}

class PanelsContainer(ctx: Context, val host: Host) : LinearLayout(ctx) {
    private var dragIdx = -1
    private var startX = 0f
    private var startRatios = DoubleArray(0)

    init {
        orientation = LinearLayout.HORIZONTAL
        setBackgroundColor(C_BG)
    }

    fun rebuild() {
        removeAllViews()
        val ps = Store.panels
        for (i in 0 until ps.size) {
            if (i > 0) {
                addView(DividerView(context, i - 1, this), LinearLayout.LayoutParams(context.dp(10), MATCH))
            }
            val pv = PanelView(context, host, ps[i], false)
            addView(pv, LinearLayout.LayoutParams(0, MATCH, ps[i].ratio.toFloat()))
        }
    }

    fun dragStart(i: Int, rawX: Float) {
        dragIdx = i
        startX = rawX
        startRatios = DoubleArray(Store.panels.size) { Store.panels[it].ratio }
    }

    fun dragMove(rawX: Float) {
        val i = dragIdx
        if (i < 0) return
        val j = i + 1
        if (j >= Store.panels.size || j >= startRatios.size) return
        val n = Store.panels.size
        val total = maxOf(1, width - (n - 1) * context.dp(10)).toDouble()
        val delta = (rawX - startX).toDouble() / total
        val combined = startRatios[i] + startRatios[j]
        val newLeft = maxOf(MIN_RATIO, minOf(combined - MIN_RATIO, startRatios[i] + delta))
        Store.panels[i].ratio = newLeft
        Store.panels[j].ratio = combined - newLeft
        (getChildAt(2 * i).layoutParams as LinearLayout.LayoutParams).weight = newLeft.toFloat()
        (getChildAt(2 * j).layoutParams as LinearLayout.LayoutParams).weight = (combined - newLeft).toFloat()
        requestLayout()
    }

    fun dragEnd() {
        dragIdx = -1
        Store.touch(context)
    }
}

// ---------------------------------------------------------------------------
// MainActivity
// ---------------------------------------------------------------------------
class MainActivity : Activity(), Host {
    private var container: PanelsContainer? = null
    private var pendingPanel = -1
    private var fromOverlay = false
    private var wrapBtn: Button? = null
    private var sBtn: Button? = null

    override val isOverlay: Boolean get() = false

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        Store.ensureLoaded(this)
        buildUi()
        val wantsPick = intent != null && intent.getStringExtra("pick") != null
        if (wantsPick) {
            handlePick(intent)
        } else if (Store.fresh) {
            Store.fresh = false
            val p = Store.panels[0]
            window.decorView.post { pickFolder(p.id) }
        }
    }

    override fun onNewIntent(intent: Intent) {
        super.onNewIntent(intent)
        setIntent(intent)
        handlePick(intent)
    }

    private fun handlePick(i: Intent?) {
        if (i == null) return
        val pick = i.getStringExtra("pick") ?: return
        val pid = i.getIntExtra("panel", -1)
        fromOverlay = i.getBooleanExtra("fromOverlay", false)
        i.removeExtra("pick")
        if (pick == "open") pickOpen(pid) else pickFolder(pid)
    }

    override fun onPause() {
        super.onPause()
        Store.persistAsync(this)
    }

    private fun buildUi() {
        val col = LinearLayout(this)
        col.orientation = LinearLayout.VERTICAL
        col.setBackgroundColor(C_BG)

        val bar = HorizontalScrollView(this)
        bar.setBackgroundColor(C_HEAD)
        bar.isHorizontalScrollBarEnabled = false
        val row = LinearLayout(this)
        row.orientation = LinearLayout.HORIZONTAL
        row.gravity = Gravity.CENTER_VERTICAL
        row.setPadding(dp(6), dp(4), dp(6), dp(4))
        val title = TextView(this)
        title.text = "✦ TextPad"
        title.setTextColor(C_GOLD)
        title.textSize = 17f
        title.setTypeface(Typeface.SERIF, Typeface.BOLD)
        title.setPadding(dp(6), 0, dp(10), 0)
        row.addView(title, LinearLayout.LayoutParams(WRAPC, WRAPC))
        fun add(b: View) {
            val lp = LinearLayout.LayoutParams(WRAPC, WRAPC)
            lp.setMargins(dp(3), 0, dp(3), 0)
            row.addView(b, lp)
        }
        add(mkBtn(this, "＋ Add Folder Panel", C_BTN, C_TXT, 13f) {
            val p = Store.addPanel()
            container?.rebuild()
            Store.touch(this)
            pickFolder(p.id)
        })
        val wb = mkBtn(this, "", C_BTN, C_TXT, 13f) { }
        val sb = mkBtn(this, "", C_BTN, C_TXT, 13f) { }
        wrapBtn = wb
        sBtn = sb
        wb.setOnClickListener {
            Store.wrap = !Store.wrap
            Store.savePrefs(this)
            for (p in Store.panels) {
                for (t in p.tabs) {
                    t.hx = 0
                    t.topPos = t.doc.lineStartNear(t.topPos)
                }
            }
            updateToggles()
            Store.invalidateAll()
        }
        sb.setOnClickListener {
            Store.saveOnS = !Store.saveOnS
            Store.savePrefs(this)
            updateToggles()
            for (v in ArrayList(Store.views)) v.updateStatus()
        }
        add(wb)
        add(sb)
        add(mkBtn(this, "A−", C_UR, C_TXT, 13f) { zoom(-1f) })
        add(mkBtn(this, "A+", C_UR, C_TXT, 13f) { zoom(1f) })
        bar.addView(row, FrameLayout.LayoutParams(WRAPC, WRAPC))
        updateToggles()

        val pc = PanelsContainer(this, this)
        container = pc
        col.addView(bar, LinearLayout.LayoutParams(MATCH, WRAPC))
        col.addView(pc, LinearLayout.LayoutParams(MATCH, 0, 1f))
        setContentView(col)
        pc.rebuild()
    }

    private fun zoom(d: Float) {
        Store.fontSp = (Store.fontSp + d).coerceIn(8f, 48f)
        Store.savePrefs(this)
        Store.invalidateAll()
    }

    private fun updateToggles() {
        wrapBtn?.text = "Wrap: " + (if (Store.wrap) "ON" else "OFF")
        sBtn?.text = "S-key save: " + (if (Store.saveOnS) "ON" else "OFF")
    }

    override fun dispatchKeyEvent(event: KeyEvent): Boolean {
        if (event.action == KeyEvent.ACTION_DOWN && event.keyCode == KeyEvent.KEYCODE_T &&
            event.isCtrlPressed && event.isShiftPressed && event.repeatCount == 0) {
            if (Store.panels.isNotEmpty()) toggleTop(Store.panels[0].id)
            return true
        }
        return super.dispatchKeyEvent(event)
    }

    // ----- Host -----
    override fun pickFolder(panelId: Int) {
        pendingPanel = panelId
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT_TREE)
        i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION or
            Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION or Intent.FLAG_GRANT_PREFIX_URI_PERMISSION)
        try {
            startActivityForResult(i, 101)
        } catch (e: Exception) {
            toast("No folder picker available")
        }
    }

    override fun pickOpen(panelId: Int) {
        pendingPanel = panelId
        val i = Intent(Intent.ACTION_OPEN_DOCUMENT)
        i.addCategory(Intent.CATEGORY_OPENABLE)
        i.type = "*/*"
        i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION)
        try {
            startActivityForResult(i, 102)
        } catch (e: Exception) {
            toast("No file picker available")
        }
    }

    override fun toggleTop(panelId: Int) {
        if (OverlayService.running && OverlayService.panelId == panelId) {
            val s = Intent(this, OverlayService::class.java)
            s.putExtra("stop", true)
            startService(s)
            return
        }
        if (!Settings.canDrawOverlays(this)) {
            toast("Allow 'Display over other apps' for TextPad, then press Top again")
            try {
                startActivity(Intent(Settings.ACTION_MANAGE_OVERLAY_PERMISSION, Uri.parse("package:" + packageName)))
            } catch (e: Exception) {
            }
            return
        }
        Store.persistAsync(this)
        val s = Intent(this, OverlayService::class.java)
        s.putExtra("panel", panelId)
        startForegroundService(s)
        moveTaskToBack(true)
    }

    override fun panelsChanged() {
        container?.rebuild()
    }

    override fun dialogContext(): Context = this

    override fun showDialog(d: AlertDialog) {
        d.show()
    }

    override fun toast(msg: String) {
        Toast.makeText(this, msg, Toast.LENGTH_SHORT).show()
    }

    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        val uri = data?.data
        val p = Store.panelById(pendingPanel)
        if (resultCode == RESULT_OK && uri != null && p != null) {
            if (requestCode == 101) {
                try {
                    contentResolver.takePersistableUriPermission(uri,
                        Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION)
                } catch (e: Exception) {
                }
                p.folderUri = uri.toString()
                p.folderName = try {
                    DocumentsContract.getTreeDocumentId(uri)
                } catch (e: Exception) {
                    uri.toString()
                }
                Store.refreshPanel(p.id)
                Store.touch(this)
            } else if (requestCode == 102) {
                openFileInto(p, uri)
            }
        }
        if (fromOverlay) {
            fromOverlay = false
            moveTaskToBack(true)
        }
    }

    private fun displayName(ctx: Context, uri: Uri): String {
        try {
            val c = ctx.contentResolver.query(uri, arrayOf(OpenableColumns.DISPLAY_NAME), null, null, null)
            if (c != null) {
                try {
                    if (c.moveToFirst()) {
                        val n = c.getString(0)
                        if (n != null && n.isNotEmpty()) return n
                    }
                } finally {
                    c.close()
                }
            }
        } catch (e: Exception) {
        }
        return "Untitled"
    }

    private fun openFileInto(p: PanelData, uri: Uri) {
        try {
            contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION)
        } catch (e: Exception) {
        }
        val app = applicationContext
        toast("Opening...")
        Thread {
            try {
                val d = Doc.openUri(app, uri)
                val name = displayName(app, uri)
                UI.post {
                    val t = Tab(name, uri.toString(), d)
                    p.tabs.add(t)
                    p.active = p.tabs.size - 1
                    Store.refreshPanel(p.id)
                    Store.touch(app)
                }
            } catch (e: Throwable) {
                val msg = e.message ?: e.toString()
                UI.post { toast("Open error: " + msg) }
            }
        }.start()
    }
}

// ---------------------------------------------------------------------------
// Floating "always on top" window (draw-over-other-apps overlay).
// Drag the title bar to move it; drag any edge/corner (mouse or finger) to resize.
// ---------------------------------------------------------------------------
class OverlayRoot(ctx: Context, val wm: WindowManager, val lp: WindowManager.LayoutParams, val onGeom: () -> Unit) : FrameLayout(ctx) {
    private var dragEdge = 0
    private var sx = 0f
    private var sy = 0f
    private var ox = 0
    private var oy = 0
    private var ow = 0
    private var oh = 0
    private val grab = ctx.dp(12)
    private val corner = ctx.dp(30)
    private val minW = ctx.dp(200)
    private val minH = ctx.dp(160)
    private val gripPaint = Paint(Paint.ANTI_ALIAS_FLAG)

    private fun edgeAt(x: Float, y: Float): Int {
        var f = 0
        val w = width.toFloat()
        val h = height.toFloat()
        if (x < grab.toFloat()) f = f or 1
        if (y < grab.toFloat()) f = f or 2
        if (x > w - grab.toFloat()) f = f or 4
        if (y > h - grab.toFloat()) f = f or 8
        if (x < corner.toFloat() && y > h - corner.toFloat()) f = 9
        if (x > w - corner.toFloat() && y > h - corner.toFloat()) f = 12
        return f
    }

    override fun onInterceptTouchEvent(e: MotionEvent): Boolean {
        if (e.actionMasked == MotionEvent.ACTION_DOWN) {
            val f = edgeAt(e.x, e.y)
            if (f != 0) {
                dragEdge = f
                sx = e.rawX
                sy = e.rawY
                ox = lp.x
                oy = lp.y
                ow = lp.width
                oh = lp.height
                return true
            }
        }
        return false
    }

    override fun onTouchEvent(e: MotionEvent): Boolean {
        if (dragEdge == 0) return super.onTouchEvent(e)
        when (e.actionMasked) {
            MotionEvent.ACTION_MOVE -> resize(e.rawX - sx, e.rawY - sy)
            MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                dragEdge = 0
                onGeom()
            }
        }
        return true
    }

    private fun resize(dx: Float, dy: Float) {
        val dm = resources.displayMetrics
        var nx = ox
        var ny = oy
        var nw = ow
        var nh = oh
        val idx = dx.toInt()
        val idy = dy.toInt()
        if ((dragEdge and 4) != 0) nw = maxOf(minW, ow + idx)
        if ((dragEdge and 1) != 0) {
            val w2 = maxOf(minW, ow - idx)
            nx = ox + (ow - w2)
            nw = w2
        }
        if ((dragEdge and 8) != 0) nh = maxOf(minH, oh + idy)
        if ((dragEdge and 2) != 0) {
            val h2 = maxOf(minH, oh - idy)
            ny = oy + (oh - h2)
            nh = h2
        }
        nw = minOf(nw, dm.widthPixels)
        nh = minOf(nh, dm.heightPixels)
        lp.x = nx
        lp.y = maxOf(0, ny)
        lp.width = nw
        lp.height = nh
        try {
            wm.updateViewLayout(this, lp)
        } catch (e: Exception) {
        }
    }

    override fun onResolvePointerIcon(event: MotionEvent, pointerIndex: Int): PointerIcon? {
        val f = edgeAt(event.getX(pointerIndex), event.getY(pointerIndex))
        val type: Int = when (f) {
            1, 4 -> PointerIcon.TYPE_HORIZONTAL_DOUBLE_ARROW
            2, 8 -> PointerIcon.TYPE_VERTICAL_DOUBLE_ARROW
            3, 12 -> PointerIcon.TYPE_TOP_LEFT_DIAGONAL_DOUBLE_ARROW
            6, 9 -> PointerIcon.TYPE_TOP_RIGHT_DIAGONAL_DOUBLE_ARROW
            else -> return super.onResolvePointerIcon(event, pointerIndex)
        }
        return PointerIcon.getSystemIcon(context, type)
    }

    override fun dispatchDraw(canvas: Canvas) {
        super.dispatchDraw(canvas)
        gripPaint.color = C_GOLD
        gripPaint.strokeWidth = context.dpf(1.5f)
        val w = width.toFloat()
        val h = height.toFloat()
        val d = context.dpf(4f)
        for (k in 1..3) {
            val o = k.toFloat() * d
            canvas.drawLine(w - 2f - o, h - 2f, w - 2f, h - 2f - o, gripPaint)
        }
    }
}

class OverlayService : Service(), Host {
    companion object {
        @Volatile var running = false
        @Volatile var panelId = -1
    }

    private var wm: WindowManager? = null
    private var root: OverlayRoot? = null
    private var params: WindowManager.LayoutParams? = null
    private val alphas = floatArrayOf(1.0f, 0.85f, 0.7f, 0.55f)
    private var dsx = 0f
    private var dsy = 0f
    private var dox = 0
    private var doy = 0

    override val isOverlay: Boolean get() = true

    override fun onBind(intent: Intent?): IBinder? = null

    private fun startFg() {
        val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
        nm.createNotificationChannel(NotificationChannel("tp_overlay", "TextPad floating window", NotificationManager.IMPORTANCE_LOW))
        val pi = PendingIntent.getActivity(this, 0, Intent(this, MainActivity::class.java),
            PendingIntent.FLAG_IMMUTABLE or PendingIntent.FLAG_UPDATE_CURRENT)
        val n = Notification.Builder(this, "tp_overlay")
            .setContentTitle("TextPad is floating on screen")
            .setContentText("Tap to open the app")
            .setSmallIcon(android.R.drawable.ic_menu_edit)
            .setContentIntent(pi)
            .setOngoing(true)
            .build()
        if (Build.VERSION.SDK_INT >= 34) {
            startForeground(1, n, ServiceInfo.FOREGROUND_SERVICE_TYPE_SPECIAL_USE)
        } else {
            startForeground(1, n)
        }
    }

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        startFg()
        if (intent != null && intent.getBooleanExtra("stop", false)) {
            stopSelf()
            return START_NOT_STICKY
        }
        if (!Settings.canDrawOverlays(this)) {
            stopSelf()
            return START_NOT_STICKY
        }
        Store.ensureLoaded(this)
        val pid = if (intent == null) -1 else intent.getIntExtra("panel", -1)
        if (pid >= 0) panelId = pid
        showOverlay()
        return START_NOT_STICKY
    }

    private fun saveGeom() {
        val p = params ?: return
        Store.prefs(this).edit().putInt("ow", p.width).putInt("oh", p.height).putInt("ox", p.x).putInt("oy", p.y).apply()
    }

    private fun cycleAlpha() {
        val p = params ?: return
        val sp = Store.prefs(this)
        val i = (sp.getInt("oa", 0) + 1) % alphas.size
        sp.edit().putInt("oa", i).apply()
        p.alpha = alphas[i]
        val r = root ?: return
        try {
            wm?.updateViewLayout(r, p)
        } catch (e: Exception) {
        }
    }

    private fun openApp() {
        val i = Intent(this, MainActivity::class.java)
        i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
        startActivity(i)
        stopSelf()
    }

    private fun removeOverlay() {
        val r = root
        if (r != null) {
            try {
                wm?.removeView(r)
            } catch (e: Exception) {
            }
        }
        root = null
    }

    private fun showOverlay() {
        removeOverlay()
        val pd: PanelData? = Store.panelById(panelId) ?: (if (Store.panels.isEmpty()) null else Store.panels[0])
        if (pd == null) {
            stopSelf()
            return
        }
        panelId = pd.id
        val wmgr = getSystemService(Context.WINDOW_SERVICE) as WindowManager
        wm = wmgr
        val sp = Store.prefs(this)
        val dm = resources.displayMetrics
        val w = sp.getInt("ow", dp(340)).coerceIn(dp(200), dm.widthPixels)
        val h = sp.getInt("oh", dp(440)).coerceIn(dp(160), dm.heightPixels)
        val lp = WindowManager.LayoutParams(w, h, WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY,
            WindowManager.LayoutParams.FLAG_NOT_TOUCH_MODAL, PixelFormat.TRANSLUCENT)
        lp.gravity = Gravity.TOP or Gravity.START
        lp.x = sp.getInt("ox", dp(20))
        lp.y = sp.getInt("oy", dp(80))
        lp.alpha = alphas[sp.getInt("oa", 0).coerceIn(0, alphas.size - 1)]
        lp.softInputMode = WindowManager.LayoutParams.SOFT_INPUT_ADJUST_NOTHING
        params = lp

        val rootView = OverlayRoot(this, wmgr, lp) { saveGeom() }
        val g = dp(12)
        rootView.setPadding(g, g, g, g)
        rootView.setBackgroundColor(C_DIVH)

        val col = LinearLayout(this)
        col.orientation = LinearLayout.VERTICAL
        col.setBackgroundColor(C_BG)

        val bar = LinearLayout(this)
        bar.orientation = LinearLayout.HORIZONTAL
        bar.gravity = Gravity.CENTER_VERTICAL
        bar.setBackgroundColor(C_HEAD)
        val title = TextView(this)
        title.text = "✦ TextPad  ⠿ drag here"
        title.setTextColor(C_GOLD)
        title.textSize = 13f
        title.typeface = Typeface.MONOSPACE
        title.setSingleLine(true)
        title.setPadding(dp(8), dp(8), dp(8), dp(8))
        bar.addView(title, LinearLayout.LayoutParams(0, WRAPC, 1f))
        val blp = LinearLayout.LayoutParams(WRAPC, WRAPC)
        blp.setMargins(dp(2), dp(2), dp(2), dp(2))
        bar.addView(mkBtn(this, "α", C_BTN, C_TXT, 13f) { cycleAlpha() }, blp)
        bar.addView(mkBtn(this, "↗ App", C_BTN, C_TXT, 13f) { openApp() }, blp)
        bar.addView(mkBtn(this, "✕", C_RMBG, C_RMFG, 13f) { stopSelf() }, blp)
        bar.setOnTouchListener { _, e ->
            when (e.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    dsx = e.rawX
                    dsy = e.rawY
                    dox = lp.x
                    doy = lp.y
                    true
                }
                MotionEvent.ACTION_MOVE -> {
                    val dmm = resources.displayMetrics
                    lp.x = (dox + (e.rawX - dsx).toInt()).coerceIn(-(lp.width - dp(90)), dmm.widthPixels - dp(90))
                    lp.y = (doy + (e.rawY - dsy).toInt()).coerceIn(0, maxOf(0, dmm.heightPixels - dp(60)))
                    try {
                        wmgr.updateViewLayout(rootView, lp)
                    } catch (ex: Exception) {
                    }
                    true
                }
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    saveGeom()
                    true
                }
                else -> false
            }
        }
        col.addView(bar, LinearLayout.LayoutParams(MATCH, WRAPC))
        col.addView(PanelView(this, this, pd, true), LinearLayout.LayoutParams(MATCH, 0, 1f))
        rootView.addView(col, FrameLayout.LayoutParams(MATCH, MATCH))
        try {
            wmgr.addView(rootView, lp)
            root = rootView
            running = true
        } catch (e: Exception) {
            Toast.makeText(this, "Cannot show floating window: " + (e.message ?: ""), Toast.LENGTH_LONG).show()
            stopSelf()
        }
    }

    override fun onDestroy() {
        removeOverlay()
        running = false
        Store.persistAsync(this)
        super.onDestroy()
    }

    // ----- Host -----
    override fun pickFolder(panelId: Int) {
        launchPicker("folder", panelId)
    }

    override fun pickOpen(panelId: Int) {
        launchPicker("open", panelId)
    }

    private fun launchPicker(kind: String, pid: Int) {
        val i = Intent(this, MainActivity::class.java)
        i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
        i.putExtra("pick", kind)
        i.putExtra("panel", pid)
        i.putExtra("fromOverlay", true)
        try {
            startActivity(i)
        } catch (e: Exception) {
            toast("Open the TextPad app once, then try again")
        }
    }

    override fun toggleTop(panelId: Int) {
    }

    override fun panelsChanged() {
    }

    override fun dialogContext(): Context = ContextThemeWrapper(this, android.R.style.Theme_Material_Dialog_Alert)

    override fun showDialog(d: AlertDialog) {
        d.window?.setType(WindowManager.LayoutParams.TYPE_APPLICATION_OVERLAY)
        d.show()
    }

    override fun toast(msg: String) {
        Toast.makeText(this, msg, Toast.LENGTH_SHORT).show()
    }
}
