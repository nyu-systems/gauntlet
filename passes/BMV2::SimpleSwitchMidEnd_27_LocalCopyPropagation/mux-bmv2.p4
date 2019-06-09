--- before_pass
+++ after_pass
@@ -14,29 +14,18 @@ control Ing(inout Headers headers, inout
     }
 }
 control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
-    bit<32> _sub_0;
     bit<64> res_0;
     bit<32> tmp;
-    bool p_1;
     bit<64> val;
-    bool cond;
-    bool pred;
     @name("Eg.update") action update() {
-        p_1 = true;
         val = res_0;
-        _sub_0 = val[31:0];
         {
             {
-                cond = p_1;
-                pred = cond;
-                tmp = (pred ? _sub_0 : tmp);
-                cond = !cond;
-                pred = cond;
-                tmp = (pred ? 32w1 : tmp);
+                tmp = (true ? res_0[31:0] : tmp);
+                tmp = (!true ? 32w1 : tmp);
             }
         }
-        _sub_0 = tmp;
-        val[31:0] = _sub_0;
+        val[31:0] = tmp;
         res_0 = val;
     }
     apply {
