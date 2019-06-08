--- before_pass
+++ after_pass
@@ -14,29 +14,18 @@ control Ing(inout Headers headers, inout
     }
 }
 control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
-    bit<32> _sub;
     bit<64> res;
     bit<32> tmp_0;
-    bool p_1;
     bit<64> val;
-    bool cond;
-    bool pred;
     @name("Eg.update") action update_0() {
-        p_1 = true;
         val = res;
-        _sub = val[31:0];
         {
             {
-                cond = p_1;
-                pred = cond;
-                tmp_0 = (pred ? _sub : tmp_0);
-                cond = !cond;
-                pred = cond;
-                tmp_0 = (pred ? 32w1 : tmp_0);
+                tmp_0 = (true ? res[31:0] : tmp_0);
+                tmp_0 = (!true ? 32w1 : tmp_0);
             }
         }
-        _sub = tmp_0;
-        val[31:0] = _sub;
+        val[31:0] = tmp_0;
         res = val;
     }
     apply {
