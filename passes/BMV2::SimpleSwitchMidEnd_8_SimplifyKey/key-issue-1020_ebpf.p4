--- before_pass
+++ after_pass
@@ -48,12 +48,14 @@ control pipe(inout Headers_t headers, ou
     @name("pipe.drop") action drop() {
         pass = false;
     }
+    bit<32> key_0;
+    bit<32> key_1;
     @name("pipe.t") table t_0 {
         key = {
-            headers.ipv4.srcAddr + 32w1: exact @name(" headers.ipv4.srcAddr") ;
-            headers.ipv4.dstAddr + 32w1: exact @name("headers.ipv4.dstAddr") ;
-            headers.ethernet.dstAddr   : exact @name("headers.ethernet.dstAddr") ;
-            headers.ethernet.srcAddr   : exact @name("headers.ethernet.srcAddr") ;
+            key_0                   : exact @name(" headers.ipv4.srcAddr") ;
+            key_1                   : exact @name("headers.ipv4.dstAddr") ;
+            headers.ethernet.dstAddr: exact @name("headers.ethernet.dstAddr") ;
+            headers.ethernet.srcAddr: exact @name("headers.ethernet.srcAddr") ;
         }
         actions = {
             invalidate();
@@ -63,7 +65,11 @@ control pipe(inout Headers_t headers, ou
         default_action = drop();
     }
     apply {
-        tmp = t_0.apply().hit;
+        {
+            key_0 = headers.ipv4.srcAddr + 32w1;
+            key_1 = headers.ipv4.dstAddr + 32w1;
+            tmp = t_0.apply().hit;
+        }
     }
 }
 ebpfFilter<Headers_t>(prs(), pipe()) main;
