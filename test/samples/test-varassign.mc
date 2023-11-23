component Application provides App {

  var gn = 4+4+4 : int;

  def main() : int {
  
  	print(gn); //12
  	
	var ref = &gn : &int;
	ref++;
	print(gn); //13
	
	var k = ++gn : int;
	print(k); //14
  }
}
