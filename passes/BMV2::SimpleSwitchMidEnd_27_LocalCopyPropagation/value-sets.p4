--- before_pass
+++ after_pass
@@ -12,7 +12,6 @@ extern ValueSet {
     bit<8> index(in bit<16> proto);
 }
 parser TopParser(packet_in b, out Parsed_packet p) {
-    bit<8> setIndex_0;
     bit<8> tmp;
     @name("TopParser.ethtype_kinds") ValueSet(32w5) ethtype_kinds_0;
     state start {
@@ -26,8 +25,7 @@ parser TopParser(packet_in b, out Parsed
     }
     state dispatch_value_sets {
         tmp = ethtype_kinds_0.index(p.ethernet.etherType);
-        setIndex_0 = tmp;
-        transition select(setIndex_0) {
+        transition select(tmp) {
             8w1: parse_trill;
             8w2: parse_vlan_tag;
         }
