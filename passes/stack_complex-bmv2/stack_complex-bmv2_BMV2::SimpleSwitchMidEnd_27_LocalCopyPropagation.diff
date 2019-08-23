--- before_pass
+++ after_pass
@@ -14,7 +14,7 @@ parser p(packet_in b, out Headers h, ino
     state start {
         b.extract<hdr>(h.hs.next);
         m.v = h.hs.last.f2;
-        m.v = m.v + h.hs.last.f2;
+        m.v = h.hs.last.f2 + h.hs.last.f2;
         transition select(h.hs.last.f1) {
             32w0: start;
             default: accept;
