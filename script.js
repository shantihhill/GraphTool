console.log("START ALL");

var nodeCnt = 0, edgeCnt = 0;
var edges = [], newEdges = [];
var nodes = [], newNodes = [];
var mapNd = {};

//canvas initialization + constants;
var ndRad = 30, edgeIdealLength = 150, edgePrcIncr = 0.035, defNdRad = 30;
var lineWidth = 3, arcLineWidth = 5, thickArcLineWidth = 14;
var cnvSz = 800, cnv, ctx;
var mX, mY, fX, fY, time = 0, clickTime = 25, directed = 0;
var graphMode = "gravity";
var dirTriLen = 30, zeroLimit = 1e-10, maxInt = Number.MAX_SAFE_INTEGER;
var disWE = 20, randLenInt = 100, textDiffMark = 80, clickEdgeDist = 10;
var inpX = 0, inpY = 0, inpMaxTop = 39, inpMaxLeft = 36, inpBox;
var drwX = 0, drwY = 0, drwId = -1;
cnv = document.getElementById("myCanvas");
ctx = cnv.getContext("2d");
cnv.width = cnvSz;
cnv.height = cnvSz;
var cx = cnvSz / 2, cy = cnvSz / 2, ct = 0;
var ncF = 0.0008, nnF = 100000, edF = 0.003, fErr = 0.00001, edDistErr = 15;
var ndEffRad = 160, dragF = 0.2, maxVel = 5, dragRate = 0.96; 
var FPS = 100, fpsInterval, now, then, elapsed;
var maxNodeRad = 100, maxLeng = 1000000;

//for highlight, paths, tree
var nrEd = [], vecNd = [], vecEd = [], seen = [], zEd = [], height = [], leaf = [];
var above = [], colorSet = [], stkEd = [], stkNd = [], estq = [], low = [], dist = [];
var shuffle = [], edMF = [], dad = [];
var stepX, stepY, nrLeaf, topN, stkEdTp, stkNdTp, nrC;
var mnCC = 0, mxCC = 321, pathPlay = 1, crrOp = 0, nrOp;
var pathOpQue = [];
var firstCol = "#FF0000", secondCol = "#00FF00", pathMode = 0, pathHigh = 0, pathAlg, sMF, fMF;
var FPS2 = 1.5, fpsInterval2, now2, then2, elapsed2, minFPS2 = 0.5, maxFPS2 = 8;

timeLoop();

updateGraphData();

graphInputUpdate();

makeUndirected();

selectGravity();

setFrameRate();

function isNumeric(value) {
	return /^\d+$/.test(value);
}

function updateMousePos(evt) {
	var rect = cnv.getBoundingClientRect();
	var scaleX = cnv.width / rect.width;
	var scaleY = cnv.height / rect.height;
	mX = (evt.clientX - rect.left) * scaleX;
	mY = (evt.clientY - rect.top) * scaleY;
}

function quadraticSolve(a, b, c) {
	var d = b * b - 4 * a * c, ans;
	if (a == 0) {
		if (b == 0) return ans;	
		if (c == 0) {
			ans = [0];
			return ans;
		}
		ans = [-c / b];
		return ans;
	}
	if (d < 0) {
		return ans;
	}
	if (d == 0) {
		ans = [-b / 2 * a];
		return ans;
	}
	d = Math.sqrt(d);
	ans = [(-b + d) / 2 * a, (-b - d) / 2 * a];
	return ans;
}

function cuberoot(x) {
  var y = Math.pow(Math.abs(x), 1/3);
  return x < 0 ? -y : y;
} 

function nextIntNumb() {
	for (var i = 1; i <= nodeCnt; i++) {
		var ok = 0;
		for (var j = 0; j < nodeCnt; j++)
			if (nodes[j].name == i)	ok = 1;
		if (ok == 1)	continue;
		return i;	
	}
	return nodeCnt + 1;
}

function cubicSolve(a, b, c, d) {
	var x1, x2, x3, ans;
  if (a == 0) {
		ans = quadraticSolve(b, c, d);
    return ans;
  } //End if a == 0
  if (d == 0) {
		ans = quadraticSolve(a, b, c);
		if (ans == undefined)	ans = [0];
		else ans[ans.length] = 0;
    return ans;
  } //End if d == 0
	var p = (3 * a * c - b * b)/(3 * a * a);
  var q = (2 * b * b * b - 9 * a * b * c + 27 * a * a * d)/(27 * a * a * a);
  var roots;

  if (Math.abs(p) < 1e-8) { // p = 0 -> t^3 = -q -> t = -q^1/3
    roots = [cuberoot(-q)];
  } else if (Math.abs(q) < 1e-8) { // q = 0 -> t^3 + pt = 0 -> t(t^2+p)=0
  roots = [0].concat(p < 0 ? [Math.sqrt(-p), -Math.sqrt(-p)] : []);
  } else {
    var D = q * q / 4 + p * p * p / 27;
    if (Math.abs(D) < 1e-8) {       // D = 0 -> two roo5s
      roots = [-1.5 * q / p, 3 * q / p];
    } else if (D > 0) {             // Only one real root
      var u = cuberoot(-q / 2 - Math.sqrt(D));
      roots = [u - p / (3 * u)];
    } else {                        // D < 0, three roots, but needs to use complex numbers/trigonometric solution
      var u = 2 * Math.sqrt(-p / 3);
      var t = Math.acos(3 * q / p / u) / 3;  // D < 0 implies p < 0 and acos argument in [-1..1]
      var k = 2 * Math.PI / 3;
      roots = [u * Math.cos(t), u * Math.cos(t-k), u * Math.cos(t - 2 * k)];
    }
	}
   // Convert back from depressed cubic
  for (var i = 0; i < roots.length; i++)
    roots[i] -= b / (3 * a);
  return roots;	
}  //End of cubicSolve

function distPointBezier(x, y, id) {
	var x0 = nodes[mapNd[edges[id].first]].posX;
	var y0 = nodes[mapNd[edges[id].first]].posY;
	var x2 = nodes[mapNd[edges[id].second]].posX;
	var y2 = nodes[mapNd[edges[id].second]].posY;
	var x1 = 2 * edges[id].trdX - x0 / 2 - x2 / 2;
	var y1 = 2 * edges[id].trdY - y0 / 2 - y2 / 2;
	var P0 = new Object(), P1 = new Object(), P2 = new Object(), M = new Object(), Ms = new Object(), A = new Object(), B = new Object();
	P0.x = x0;
	P0.y = y0;
	P1.x = x1;
	P1.y = y1;
	P2.x = x2;
	P2.y = y2;
	M.x = x;
	M.y = y;
	Ms.x = P0.x - M.x;
	Ms.y = P0.y - M.y;
	A.x = P1.x - P0.x;
	A.y = P1.y - P0.y;
	B.x = P2.x - P1.x - A.x;
	B.y = P2.y - P1.y - A.y;
	var a, b, c, d;	
	a = (B.x * B.x) + (B.y * B.y);
	b = 3 * ((A.x * B.x) + (A.y * B.y));		
	c = 2 * ((A.x * A.x) + (A.y * A.y)) + (Ms.x * B.x) + (Ms.y * B.y);
	d = (Ms.x * A.x) + (Ms.y * A.y);
	//at^3 + bt^2 + ct + d = 0;
	var rz, distMin = maxInt, xx, yy;
	rz = cubicSolve(a, b, c, d);
	
	for (var i = 0; i < rz.length; i++) {		
		if (rz[i] < 0)	rz[i] = 0;
		if (rz[i] > 1)	rz[i] = 1;
		xx = (1 - rz[i]) * (1 - rz[i]) * P0.x + 2 * (1 - rz[i]) * rz[i] * P1.x + rz[i] * rz[i] * P2.x;
		yy = (1 - rz[i]) * (1 - rz[i]) * P0.y + 2 * (1 - rz[i]) * rz[i] * P1.y + rz[i] * rz[i] * P2.y;
		if (Math.sqrt(distAB(x, y, xx, yy)) < distMin) {
			distMin = Math.sqrt(distAB(x, y, xx, yy));
		}
	}
	return distMin;
}

function drawSmallCircle(x, y, sz) {
	//console.log("am desenat circle");
	ctx.beginPath();
	ctx.moveTo(x, y);
	ctx.arc(x, y, sz, 0, 2 * Math.PI);
	ctx.strokeStyle = "black";
	ctx.stroke();
}

function timeLoop() {
	time++;
//	console.log("timpul global: " + time);
	requestAnimationFrame(timeLoop);
}

function swapNodes(a, b) {
	var c = nodes[a].name;
	nodes[a].name = nodes[b].name;
	nodes[b].name = c;
	var c = nodes[a].posX;
	nodes[a].posX = nodes[b].posX;
	nodes[b].posX = c;
	var c = nodes[a].posY;
	nodes[a].posY = nodes[b].posY;
	nodes[b].posY = c;
	var c = nodes[a].vX;
	nodes[a].vX = nodes[b].vX;
	nodes[b].vX = c;
	var c = nodes[a].vY;
	nodes[a].vY = nodes[b].vY;
	nodes[b].vY = c;
}

function mouseOut() {
	console.log("mouse out ba pula");
}

function isNumber(n) { return /^-?[\d.]+(?:e-?\d+)?$/.test(n); }

function distAB(x, y, a, b) {
	return (x - a) * (x - a) + (y - b) * (y - b);
}

function distPointEdge(px, py, i) {
	var x0 = nodes[mapNd[edges[i].first]].posX;
	var y0 = nodes[mapNd[edges[i].first]].posY;
	var x1 = nodes[mapNd[edges[i].second]].posX;
	var y1 = nodes[mapNd[edges[i].second]].posY;
	var mx = (x0 + x1) / 2, my = (y0 + y1) / 2;
	if (x1 != x0) {
		var a0 = (y1 - y0) / (x1 - x0);
		var b0 = y0 - x0 * a0;	
	} else {
		var a0 = "nu";
		var b0 = "nu";
	}
	if (edges[i].trdX == mx && edges[i].trdY == my) {
		return distToLine(px, py, a0, b0, x0, y0, x1, y1);	
	}
	return distPointBezier(px, py, i);	
}

function updateInputBox(x0, y0) {
	// 0 -> 0; cnvSz -> 39,36
	console.log("am schimbat: " + x0 + y0);
	inpX = x0 * inpMaxLeft / cnvSz;
	inpY = y0 * inpMaxTop / cnvSz;
	inpBox.style["top"] = inpY + "vw";	
	inpBox.style["left"] = inpX+ "vw";
}

function deleteEdge(id) {
	var k = 0, fn = edges[id].first, sn = edges[id].second;
	for (var i = 0; i < edgeCnt - k; i++) {
		while (i + k < edgeCnt && edges[i + k].first == fn && edges[i + k].second == sn)
			k++;
		if (i + k >= edgeCnt)	continue;
		edges[i].first = edges[i + k].first;
		edges[i].second = edges[i + k].second;
		edges[i].leng = edges[i + k].leng;
		edges[i].arc = edges[i + k].arc;
		edges[i].prc = edges[i + k].prc;
		edges[i].trdX = edges[i + k].trdX;
		edges[i].trdY = edges[i + k].trdY;
		edges[i].type = edges[i + k].type;	
		edges[i].color = edges[i + k].color;
	}
	edgeCnt -= k;

	for (var i = 0; i < nodeCnt; i++) {
		var ok = 0;
		for (j = 0; j < edgeCnt; j++)
			if (edges[j].first == nodes[i].name || edges[j].second == nodes[i].name)
				ok = 1;
		if (!ok) {
			edges[edgeCnt] = new Object();
			edges[edgeCnt].prc = 0;
			edges[edgeCnt].arc = 0;
			edges[edgeCnt].trdX = 0;
			edges[edgeCnt].trdY = 0;
			edges[edgeCnt].type = 0;;
			edges[edgeCnt].leng = "";
			edges[edgeCnt].first = nodes[i].name;
			edges[edgeCnt].second = "";	
			edges[edgeCnt].color = "black";
			edgeCnt++;
		}
	}
}

function deleteNode(id) {
	var nn = nodes[id].name;
	for (var i = id; i < nodeCnt - 1; i++) {
		nodes[i].name = nodes[i + 1].name;
		nodes[i].posX = nodes[i + 1].posX;
		nodes[i].posY = nodes[i + 1].posY;
		nodes[i].vX = nodes[i + 1].vX;
		nodes[i].vY = nodes[i + 1].vY;
		nodes[i].grab = nodes[i + 1].grab;
		nodes[i].type = nodes[i + 1].type;
		nodes[i].fix = nodes[i + 1].fix;
		nodes[i].color = nodes[i + 1].color;
		mapNd[nodes[i].name] = i;
	}
	nodeCnt--;
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].first == nn || edges[i].second == nn) {
			deleteEdge(i);
			i--;
		}
	}
}

function graphInputUpdate() {
	var txt = "";
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].first	!= undefined)	txt += edges[i].first;
		if (edges[i].second != undefined) txt += " " + edges[i].second;
		if (edges[i].leng != undefined)	txt += " " + edges[i].leng;
		txt += "\n";
	}
	document.getElementById("graphData").value = txt;
	document.getElementById("nodeCount").value = nodeCnt;

	checkCycle();
	checkIsLenght();	
}

function addRandomLengths() {
	resetPlayer();
	for (var i = 0; i < edgeCnt; i++) {
		edges[i].leng = parseInt(Math.random() *	randLenInt);
	}
	graphInputUpdate();
}

function removeRandomLengths() {
	resetPlayer();
	for (var i = 0; i < edgeCnt; i++) {
		edges[i].leng = undefined;
	}
	graphInputUpdate();
}
function sortShuffle() {
	for (var i = 0; i < nodeCnt; i++) {
		nodes[i].posX = ndRad + Math.random() * (cnvSz - ndRad);
		nodes[i].posY = Math.random() * (cnvSz - ndRad);
		nodes[i].vX = 0;
		nodes[i].vY = 0;
	}
}

function makeNodeList() {
	for (var i = 0; i < nodeCnt; i++) {
		nrEd[i] = 0;
		vecNd[i] = [];
		vecEd[i] = [];
	}
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].second == undefined || edges[i].second.length == 0)	continue;
		var fn = mapNd[edges[i].first], sn = mapNd[edges[i].second];
		if (directed) {
			vecNd[fn][nrEd[fn]] = sn;
			vecEd[fn][nrEd[fn]] = i;
			nrEd[fn]++;
		} else {
			vecNd[fn][nrEd[fn]] = sn;
			vecEd[fn][nrEd[fn]] = i;
			vecNd[sn][nrEd[sn]] = fn;
			vecEd[sn][nrEd[sn]] = i;
			nrEd[fn]++;
			nrEd[sn]++;
		}
	}
}

function checkIsLenght() {
	var ok = 0;
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].leng != undefined && edges[i].leng != "") {
			ok = 1;
			break;
		}
	}
	if (ok) {
		document.getElementById("lengthStatus").innerHTML = "REMOVE LENGHTS";
		document.getElementById("lengthStatus").style.color = "red";
		document.getElementById("lengthStatus2").innerHTML = "FOUND LENGHTS";
		document.getElementById("lengthStatus2").style.color = "green";
	} else {
		document.getElementById("lengthStatus").innerHTML = "REMOVED LENGHTS";
		document.getElementById("lengthStatus").style.color = "green";
		document.getElementById("lengthStatus2").innerHTML = "MISSING LENGHTS";
		document.getElementById("lengthStatus2").style.color = "red";
	}
}

function checkCycleSearch(n) {
	seen[n] = 1;
	above[n] = 1;
	var ct = 0, rez = 0;
	for (var i = 0; i < nrEd[n]; i++) {
		var x = vecNd[n][i];
		if (above[x]) {
			ct++;
			continue;
		}
		rez |= checkCycleSearch(x);	
	}
	if (ct > 1 - directed)	rez = 1;
	above[n] = 0;
	return rez;
}

function checkCycle() {
	makeNodeList();
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;
		above[i] = 0;
	}
	var rez = 0;
	for (var i = 0; i < nodeCnt; i++) {
		if (!seen[i]) {
			rez |= checkCycleSearch(i);
		}
	}
	if (rez == 0) {
		document.getElementById("cycleStatus").innerHTML = "NO CYCLE";
		document.getElementById("cycleStatus").style.color = "green";
		document.getElementById("cycleStatus4").innerHTML = "NO CYCLE";
		document.getElementById("cycleStatus4").style.color = "green";
	}
	if (rez == 1) {
		document.getElementById("cycleStatus").innerHTML = "FOUND CYCLE";
		document.getElementById("cycleStatus").style.color = "red";
		document.getElementById("cycleStatus4").innerHTML = "FOUND CYCLE";
		document.getElementById("cycleStatus4").style.color = "red";
	}
}

function setHeightLeaf(n) {
	seen[n] = 1;
	leaf[n] = 1;
	for (var i = 0; i < nrEd[n]; i++) {
		var x = vecNd[n][i];
		if (seen[x])	continue;
		leaf[n] = 0;
		height[x] = height[n] + 1;
		setHeightLeaf(x);
	}
	if (leaf[n]) {
		nrLeaf++;
		leaf[n] = nrLeaf;
	}
}

function setTreeCoords(n) {
	console.log("intru in pizda: " + nodes[n].name);
	seen[n] = 1;
	if (leaf[n]) {
		nodes[n].posX = 2 * ndRad + stepX * (leaf[n] - 1);
		return;
	}
	var mnX = maxInt, mxX = 0;
	for (var i = 0; i < nrEd[n]; i++) {
		var x = vecNd[n][i];
		if (seen[x])	continue;
		setTreeCoords(x);
		mnX = Math.min(mnX, nodes[x].posX);
		mxX = Math.max(mxX, nodes[x].posX);
	}
	console.log("avem: " + nodes[n].name + " " + mnX + " " + mxX);
	nodes[n].posX = mnX + (mxX - mnX) / 2;
}

function sortTree() {
	if (document.getElementById("cycleStatus").style.color == "red")
		return;
	fixAll();	
	makeNodeList();
	var fh = 2 * ndRad, lh = cnvSz - 2 * ndRad;
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;
		height[i] = 0;
		leaf[i] = 0;
		low[i] = 0;
	}
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].second == undefined || edges[i].second.length == 0)	continue;
		var x = mapNd[edges[i].second];
		low[x] = 1;
	}
	nrLeaf = 0;
	for (var i = 0; i < nodeCnt; i++) {
		if (!seen[i] &&	!low[i]) {
			setHeightLeaf(i);
		}
	}
	for (var i = 0; i < nodeCnt; i++) {
		if (!seen[i]) {
			setHeightLeaf(i);
		}
	}
	var maxH = 1;
	for (var i = 0; i < nodeCnt; i++) {
		if (height[i] > maxH)	maxH = height[i];
		seen[i] = 0;
	}
	console.log("hai sa vedem: ");
	for (var i = 0; i < nodeCnt; i++) {
		console.log("avem nodull: " + nodes[i].name + " h: " + height[i]);
	}
	stepY = (lh - fh) / maxH;
	stepX = (lh - fh) / Math.max(1, nrLeaf - 1);
	for (var i = 0; i < nodeCnt; i++) {
		if (!height[i]) {
			setTreeCoords(i);
		}
		nodes[i].posY = fh + stepY * height[i];
	}
}

function topologicDFS(n) {
	seen[n] = 1;
	for (var i = 0; i < nrEd[n]; i++) {
		var x = vecNd[n][i];
		if (seen[x])	continue;
		topologicDFS(x);
	}
	seen[n] = topN;
	topN--;
}

function sortTopological() {
	makeDirected();
	if (document.getElementById("cycleStatus").style.color == "red")
		return;
	fixAll();
	makeNodeList();
	topN = nodeCnt;	
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;
	}
	for (var i = 0; i < nodeCnt; i++) {
		if (!seen[i]) {
			topologicDFS(i);	
		}
	}
	var fh = 2 * ndRad, lh = cnvSz - 2 * ndRad;
	var step = (lh - fh) / Math.max(1, nodeCnt - 1);
	for (var i = 0; i < nodeCnt; i++) {
		nodes[i].posX = fh + (seen[i] - 1) * step;
		nodes[i].posY = nodes[i].posX;
	}
}

function edgeColorReset() {
	for (var i = 0; i < edgeCnt; i++)
		edges[i].color = "black";
}
function nodeColorReset() {
	for (var i = 0; i < nodeCnt; i++) {
		nodes[i].color = "black";
	}
}

function addEdgeColor(nrCol) {
	for (var i = 1; i <= nrCol; i++) {
		shuffle[i] = i;
	}
	for (var i = 0; i < nrCol; i++) {
		var x = Math.max(1, Math.round(Math.random() * nrCol));
		var y = Math.max(1, Math.round(Math.random() * nrCol));
		var aux = shuffle[x];
		shuffle[x] = shuffle[y];
		shuffle[y] = aux;
	}
	var colStep = (mxCC - mnCC) / Math.max(1, nrCol - 1);
	for (var i = 0; i < edgeCnt; i++) {
		if (colorSet[i] == 0) {
			for (var j = 0; j < edgeCnt; j++) {
				if (colorSet[j] != 0 && i != j && edges[i].first == edges[j].first && edges[i].second == edges[j].second) {
					colorSet[i] = colorSet[j];
					break;
				}
			}
		}
		if (colorSet[i] != 0) {
			colorSet[i] = shuffle[colorSet[i]];
			var cl = mnCC + (colorSet[i] - 1) * colStep;
			edges[i].color = "hsl(" + cl + ", 100%, 50%)";
		} else {
			edges[i].color = "black";
		}
	}
}

function dfsConnComp(n, id) {
	seen[n] = 1;
	for (var i = 0; i < nrEd[n]; i++) {
		var x = vecNd[n][i];
		var y = vecEd[n][i];
		colorSet[y] = id;
		if (seen[x])	continue;
		dfsConnComp(x, id);
	}
}

function highConnComp() {
	if (directed)	return;
	makeNodeList();
	var id = 0;
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;
	}
	for (var i = 0; i < edgeCnt; i++) {
		colorSet[i] = 0;
	}
	for (var i = 0; i < nodeCnt; i++) {
		if (!seen[i]) {
			id++;
			dfsConnComp(i, id);
		}
	}
	addEdgeColor(id);
}

function bridgeEdges(n, edId) {
	seen[n] = 1;
	var mn = height[n];
	for (var i = 0; i < nrEd[n]; i++) {
		var x = vecNd[n][i];
		var y = vecEd[n][i];
		if (y == edId)	continue;
		if (seen[x]) {
			mn = Math.min(mn, height[x]);
			continue;
		}
		height[x] = height[n] + 1;
		var aux = bridgeEdges(x, y);	
		mn = Math.min(mn, aux);
	}
	if (height[n] > 1 && mn == height[n]) {
		colorSet[edId] = 1;
	}
	return mn;
}

function highBridgeEdges() {
	if (directed)	return;
	makeNodeList();
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;
		height[i] = 0;
	}
	for (var i = 0; i < edgeCnt; i++) {
		colorSet[i] = 0;
	}
	for (var i = 0; i < nodeCnt; i++) {
		if (!seen[i]) {
			height[i] = 1;
			bridgeEdges(i, -1);
		}
	}
	addEdgeColor(1);
}

function biconnComp(n, edId) {
	seen[n] = 1;
	var mn = height[n];
	stkEd[++stkEdTp] = edId;
	for (var i = 0; i < nrEd[n]; i++) {
		var x = vecNd[n][i];
		var y = vecEd[n][i];
		if (y == edId)	continue;
		if (seen[x] && height[x] < height[n]) {
			mn = Math.min(mn, height[x]);
			stkEd[++stkEdTp] = y;
			continue;
		}
		if (seen[x])	continue;

		height[x] = height[n] + 1;
		var aux = biconnComp(x, y);
		mn = Math.min(mn, aux);

		if (height[n] > 1 && mn == height[n]) {
			nrC++;	
			while (stkEdTp > 0 && stkEd[stkEdTp] != edId) {
				colorSet[stkEd[stkEdTp]] = nrC;
				stkEdTp--;
			}
		}
		if (height[n] == 1 && stkEdTp > 1) {
			nrC++;
			while (stkEdTp > 1) {
				colorSet[stkEd[stkEdTp]] = nrC;
				stkEdTp--;
			}
		}
	}
	if (height[n] > 1 && mn == height[n]) {
		nrC++;
		colorSet[edId] = nrC;
		stkEdTp--;
	}
	return mn;
}

function highBiconnComp() {
	if (directed)	return;
	makeNodeList();
	stkEdTp = 0;
	nrC = 0;
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;
		height[i] = 0;
	}
	for (var i = 0; i < edgeCnt; i++) {
		colorSet[i] = 0;
	}
	for (var i = 0; i < nodeCnt; i++) {
		if (!seen[i]) {
			height[i] = 1;
			biconnComp(i, -1);
		}
	}
	addEdgeColor(nrC);
}

function strongConn(n, edId) {
	stkEd[++stkEdTp] = edId;
	stkNd[++stkNdTp] = n;
	estq[n] = 1;
	topN++;	
	seen[n] = topN;
	low[n] = topN;
	console.log("am intrat in: " + nodes[n].name);
	for (var i = 0; i < nrEd[n]; i++) {
		var x = vecNd[n][i];
		var y = vecEd[n][i];
		if (!seen[x]) {
			strongConn(x, y);
			low[n] = Math.min(low[n], low[x]);
			continue;
		}
		if (estq[x]) {
			low[n] = Math.min(low[n], low[x]);
			stkEd[++stkEdTp] = y;
		}
	}
	console.log("incercam: " + nodes[n].name + " " + seen[n] + " " + low[n] + " " + stkEdTp);
	if (low[n] == seen[n] && stkEd[stkEdTp] != edId) {
		console.log("avem una");
		nrC++;
		while (stkEd[stkEdTp] != edId) {
			colorSet[stkEd[stkEdTp]] = nrC;
			stkEdTp--;
		}
		stkEdTp--;
		while (stkNd[stkNdTp] != n) {
			estq[stkNd[stkNdTp]] = 0;
			stkNdTp--;
		}
		estq[stkNd[stkNdTp]] = 0;
		stkNdTp--;
	}
	else if (low[n] == seen[n]) {
		stkEdTp--;
		estq[stkNd[stkNdTp]] = 0;
		stkNdTp--;
	}
}

function highStrongConn() {
	if (!directed)	return;
	makeNodeList();
	topN = 0;
	stkEdTp = 0;
	stkNdTp = 0;
	nrC = 0;
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;
		height[i] = 0;
		low[i] = 0;
		estq[i] = 0;
	}
	for (var i = 0; i < edgeCnt; i++) {
		colorSet[i] = 0;
	}
	for (var i = 0; i < nodeCnt; i++) {
		if (seen[i] == 0) {
			height[i] = 1;
			strongConn(i, -1);
		}
	}
	addEdgeColor(nrC);
}

function addPathOp(name, id, color) {
	nrOp++;
	pathOpQue[nrOp] = new Object();
	pathOpQue[nrOp].name = name;
	pathOpQue[nrOp].id = id;
	pathOpQue[nrOp].color = color;	
}

function DFS(n, edId) {
	seen[n] = 1;
	addPathOp("node", n, firstCol);
	for (var i = 0; i < nrEd[n]; i++) {
		var x = vecNd[n][i];
		var y = vecEd[n][i];
		if (y == edId)	continue;

		if (!seen[x]) {
			addPathOp("edge", y, firstCol);	
			DFS(x, y);
			addPathOp("edge", y, secondCol);
		}
	}
	addPathOp("node", n, secondCol);
}

function pathDFS() {
	if (document.getElementById("lengthStatus").style.color == "red")	return;	
	resetPlayer();
	makeNodeList();	
	pathAlg = "DFS";
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;
	}
	for (var i = 0; i < edgeCnt; i++) {
		zEd[i] = 0;
	}
}

function BFS(n) {
	var queBFS = [], queN = 0, crrN = 1;
	queBFS[++queN] = new Object();
	queBFS[queN].x = n;
	queBFS[queN].y = -1;
	seen[n] = 1;
	addPathOp("node", n, firstCol);
	while (crrN <= queN) {
		var x = queBFS[crrN].x;
		var y = queBFS[crrN].y;
		if (y != -1)	addPathOp("edge", y, secondCol);
		addPathOp("node", x, secondCol);
		crrN++;
		for (var i = 0; i < nrEd[x]; i++) {
			var nx = vecNd[x][i];
			var	ny = vecEd[x][i]; 
			if (!seen[nx]) {
				queBFS[++queN] = new Object;
				queBFS[queN].x = nx;
				queBFS[queN].y = ny;
				seen[nx] = 1;
				addPathOp("edge", ny, firstCol);
				addPathOp("node", nx, firstCol);
			}
		}
	}
}

function pathBFS() {
	if (document.getElementById("lengthStatus").style.color == "red")	return;	
	resetPlayer();
	makeNodeList();
	pathAlg = "BFS";
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;		
	}
}

function DJK(n) {

	if (nodes[n].color == firstCol || nodes[n].color == secondCol)	return;	
	var ok = 1, queN = 0, mnDis = maxInt, idDis = -1;
	estq[n] = ++queN;
	dist[n] = 0;
	zEd[n] = -1;
	addPathOp("node", n, firstCol);	
	while (ok) {
		ok = 0;
		mnDis = maxInt;	
		for (var i = 0; i < nodeCnt; i++) {
			if (low[i])	continue;
			if (!estq[i])	continue;
			if (dist[i] < mnDis)	{
				mnDis = dist[i];
				idDis = i;	
				ok = 1;
			}
			else if (dist[i] == mnDis && estq[i] < estq[idDis]) {
				idDis = i;	
			}
		}
		if (!ok)	break;	

		var x = idDis;
		low[x] = 1;
		if (zEd[x] != -1)	addPathOp("edge", zEd[x], secondCol);	
		addPathOp("node", x, secondCol);

		for (var i = 0; i < nrEd[x]; i++) {
			var vx = vecNd[x][i];
			var vy = vecEd[x][i];	
			var vz = dist[x] + parseInt(edges[vy].leng);
			if (low[vx])	continue;
			if (estq[vx] == maxInt)	{
				estq[vx] = ++queN;	
				addPathOp("edge", vy, firstCol);
				addPathOp("node", vx, firstCol);
			}
			if (vz < dist[vx]) {
				dist[vx] = vz;
				zEd[vx] = vy;
			}
		}
	}
}

function pathDJK() {
	if (document.getElementById("lengthStatus").style.color == "green") return;	
	resetPlayer();
	makeNodeList();
	pathAlg = "DJK";
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;
		dist[i] = maxInt;
		estq[i] = maxInt;
		low[i] = 0;
		zEd[i] = 0;
	}
}

function buildMF(s, f) {
	var queMF = [], n0 = 1, n1 = 0; 	
	for (var i = 0; i < nodeCnt; i++) {
		dad[i] = -1;
		zEd[i] = -1;
	}
	queMF[++n1] = s;
	dad[s] = s;
	while (n0 <= n1) {
		var x = queMF[n0];
		n0++;
		for (var i = 0; i < nrEd[x]; i++) {
			var vx = vecNd[x][i];
			if (edMF[x][vx] <= 0)	continue;
			if (dad[vx] == -1) {
				dad[vx] = x;
				zEd[vx] = vecEd[x][i];
				queMF[++n1] = vx;
			}
		}
	}
	if (dad[f] != -1)	return 1;
	return 0;
}

function updateMF(s, f) {
	var x = f, x0 = 0, z, mn = maxInt;
	while (x != s && x != -1) {
		x0 = dad[x];	
		low[x0] = x;
		mn = Math.min(mn, edMF[x0][x]);
		x = x0;
	}
	if (mn <= 0)	return;
	if (x == -1)	return;
	x = f;
	addPathOp("node", f, firstCol);
	while (x != s) {
		x0 = dad[x];
		addPathOp("edge", zEd[x], firstCol);
		addPathOp("node", x0, firstCol);
		x = x0;
	}
	x = s;
	addPathOp("node", s, secondCol);
	while (x != f) {
		x0 = x;
		x = low[x];
		edMF[x0][x] -= mn;
		addPathOp("edMF", zEd[x], mn); 
		addPathOp("node", x, secondCol);
	}
	//addPathOp("rest");
}

function MF(s, f) {
	while (buildMF(s, f)) {
		for (var i = 0; i < nodeCnt; i++) {
			for (var j = 0; j < nrEd[i]; j++) {
				if (vecNd[i][j] == f && dad[i] != f)	{
					dad[f] = i;
					zEd[f] = vecEd[i][j];
					updateMF(s, f);
					break;
				}
			}
		}
	}
}

function pathMF() {
	if (document.getElementById("lengthStatus").style.color == "green")	return;
	resetPlayer();
	makeNodeList();
	pathAlg = "MF";
	sMF = -1;
	fMF = -1;
	for (var i = 0; i < nodeCnt; i++) {
		seen[i] = 0;
		edMF[i] = [];
		for (var j = 0; j < nodeCnt; j++) {
			edMF[i][j] = 0;
		}
	}
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].second == undefined || edges[i].second.length == 0)	continue;	
		if (newEdges[i] == undefined)	newEdges[i] = new Object();
		newEdges[i].leng = edges[i].leng;
		var x1 = mapNd[edges[i].first], x2 = mapNd[edges[i].second];
		if (edges[i].leng == undefined || edges[i].leng.length == 0)	edMF[x1][x2] = 0;
		else edMF[x1][x2] = parseInt(edges[i].leng);
		if (!directed) {
			edMF[x2][x1] = edMF[x1][x2];
		}
	}
}

function butPlayPause() {
	pathPlay ^= 1;
	var btt = document.getElementById("playButt");
	btt.innerHTML = (pathPlay) ? "Pause" : "Play";
}

function nextOp() {
	crrOp++;	
	var name = pathOpQue[crrOp].name, id = pathOpQue[crrOp].id, color = pathOpQue[crrOp].color;
	if (name == "node") {
		nodes[id].color = color;
		return;
	} else if (name == "edge") {
		edges[id].color = color;
		return;
	} else if (name == "edMF") {
		edges[id].color = secondCol;
		edges[id].leng -= color;
	}
}

function undoOp() {
	if (crrOp <= 0) {
		crrOp = 0;
		return;
	}
	var name = pathOpQue[crrOp].name, id = pathOpQue[crrOp].id, color = pathOpQue[crrOp].color;
	if (name == "node") {
		if (nodes[id].color == firstCol)	nodes[id].color = "black";
		if (nodes[id].color == secondCol)	nodes[id].color = firstCol;
	} else if (name == "edge") {
		if (edges[id].color == firstCol)	edges[id].color = "black";
		if (edges[id].color == secondCol)	edges[id].color = firstCol;
	} else if (name == "edMF") {
		edges[id].color = firstCol;
		edges[id].leng += color;
	}
	crrOp--;
	if (crrOp < 0)	crrOp = 0;
	startAnimatePath();
}

function resetPlayer() {
	nrOp = 0;
	crrOp = 0;
	edgeColorReset();
	nodeColorReset();
	if (pathAlg == "MF") {
		pathAlg = "";
		for (var i = 0; i < edgeCnt; i++) {
			edges[i].leng = newEdges[i].leng;
		}
		graphInputUpdate();	
	}
}

function setFrameRate() {
	//change FPS2
	var x = parseInt(document.getElementById("myRange").value) / 100;
	FPS2 = minFPS2 + (maxFPS2 - minFPS2) * x; 
	startAnimatePath();
}

function startAnimatePath() {
	fpsInterval2 = 1000 / FPS2;
	then2 = Date.now();
	animatePath();
}

function animatePath() {
	requestAnimationFrame(animatePath);
	
	if (!pathMode) {
		nrOp = 0;
		crrOp = 0;
		if (!pathHigh) {
			edgeColorReset();
		}
		nodeColorReset();
		return;
	}
	if (!pathPlay)	return;

	now2 = Date.now();
	elapsed2 = now2 - then2;

	if (elapsed2 > fpsInterval2) {
		then2 = now2 - (elapsed2 % fpsInterval2);
		//console.log("avem frame: " + pathMode + " " + pathPlay + " " + nrOp + " " + crrOp);	
		if (crrOp < nrOp)	nextOp();	
	}
}

function makeDirected() {
	directed = 1;
	resetPlayer();
	document.getElementById("directedStatus").innerHTML = "YES DIRECTED";
	document.getElementById("directedStatus").style.color = "green";
	document.getElementById("directedStatus2").innerHTML = "NOT UNDIRECTED";
	document.getElementById("directedStatus2").style.color = "red";
	document.getElementById("directedStatus3").innerHTML = "YES DIRECTED";
	document.getElementById("directedStatus3").style.color = "green";
	checkCycle();
}
function makeUndirected() {
	directed = 0;
	resetPlayer();
	document.getElementById("directedStatus").innerHTML = "NOT DIRECTED";
	document.getElementById("directedStatus").style.color = "red";
	document.getElementById("directedStatus2").innerHTML = "YES UNDIRECTED";
	document.getElementById("directedStatus2").style.color = "green";
	document.getElementById("directedStatus3").innerHTML = "NOT DIRECTED";
	document.getElementById("directedStatus3").style.color = "red";
	checkCycle();
}

function edgeArcTarget(x0, y0, a0, b0, dis) {
	var c = new Object; 
	if (a0 == "nu") {
		c.t1X = x0 - dis;
		c.t1Y = y0;
		c.t2X = x0 + dis;
		c.t2Y = y0;
		return c;	
	} else if (Math.abs(a0) < zeroLimit) {
		c.t1X = x0;
		c.t1Y = y0 - dis;
		c.t2X = x0;
		c.t2Y = y0 + dis;
		return c;
	}
	var a1 = -1 / a0, b1 = y0 - a1 * x0;
	var qa = (1 + a1 * a1), qb = (2 * a1 * b1 - 2 * x0 - 2 * y0 * a1), qc = (x0 * x0 + y0 * y0 + b1 * b1 - 2 * y0 * b1 - dis * dis);
	var dt = Math.sqrt(Math.abs(qb * qb - 4 * qa * qc));

	c.t1X = (-qb + dt) / (2 * qa);
	c.t1Y = a1 * c.t1X + b1;
	c.t2X = (-qb - dt) / (2 * qa);
	c.t2Y = a1 * c.t2X + b1;
	return c;
}

function drawEdgeArc(i, x0, y0, x1, y1, x2, y2) {
	var dd = Math.sqrt(distAB(x0, y0, x2, y2));
	var x3 = 2 * x1 - x0 / 2 - x2 / 2;
	var y3 = 2 * y1 - y0 / 2 - y2 / 2;
	var mx = (x0 + x2) / 2, my = (y0 + y2) / 2; 
	ctx.beginPath();
	ctx.moveTo(x0, y0);	
	ctx.quadraticCurveTo(x3, y3, x2, y2);
	ctx.strokeStyle = edges[i].color;
	ctx.stroke();

	if (edges[i].leng != undefined) {
		var sx0 = x0, sy0 = y0, sx2 = x2, sy2 = y2, aux;
		var wordW = ctx.measureText(edges[i].leng).width, wordH = ctx.measureText(edges[i].leng).height;	
		var cX, cY, kX, z = disWE;
		sx0 += edges[i].trdX - mx;
		sy0 += edges[i].trdY - my;
		sx2 += edges[i].trdX - mx;
		sy2 += edges[i].trdY - my;
		if (sx0 > sx2) {
			aux = sx0, sx0 = sx2, sx2 = aux;
			aux = sy0, sy0 = sy2, sy2 = aux;
		}
		if (sx0 == sx2) {
				cX = edges[i].trdX;
				cY = edges[i].trdY;
				ctx.textAlign = "center";
		} else if (sy0 == sy2) {
				cX = edges[i].trdX;
				cY = edges[i].trdY;
				ctx.textAlign = "center";
		} else {
			var a1 = (sy2 - sy0) / (sx2 - sx0), b1 = sy0 - a1 * sx0;
			var a0 = -1 / a1, b0 = edges[i].trdY - a0 * edges[i].trdX;
			if (sy0 > sy2) {
				cX = (a1 * z + b1 - b0) / (a0 - a1);
				cY = a0 * cX + b0;
				ctx.textAlign = "right";
				
				var dx = Math.abs(sy0 - sy2), dy = Math.abs(sx0-sx2);
				if (dx < dy) {
					if (dx < textDiffMark) {
						dx = textDiffMark - dx;
						cX += wordW / 2 * dx / textDiffMark;
					}
				}
				else if (dy < dx) {
					if (dy < textDiffMark) {
						dy = textDiffMark - dy;
						cX += (wordW / 2 + disWE)  * dy / textDiffMark;	
					}
				}
			} else {
				cX = (b1 - b0 - a1 * z) / (a0 - a1);
				cY = a0 * cX + b0;
				ctx.textAlign = "left";

				var dx = Math.abs(sy0 - sy2), dy = Math.abs(sx0-sx2);
				if (dx < dy) {
					if (dx < textDiffMark) {
						dx = textDiffMark - dx;
						cX -= wordW / 2 * dx / textDiffMark;
					}
				}
				else if (dy < dx) {
					if (dy < textDiffMark) {
						dy = textDiffMark - dy;
						cX -= (wordW / 2 + disWE)  * dy / textDiffMark;	
					}
				}
			}
		}	
//		ctx.textAlign = "center";
		edges[i].lengX = cX;
		edges[i].lengY = cY;

		if (edges[i].type == 0) {
			ctx.textBaseline = "bottom";
			ctx.fillStyle = "black";
			ctx.fillText(edges[i].leng, cX, cY);
		} else {
			updateInputBox(cX, cY);	
		}
	}
	
	dirTriLen = (defNdRad + ndRad) / 2;
	if (directed && dd > dirTriLen) {
		var dmx = (cnvSz - 2 * ndRad) * Math.sqrt(2);
		x1 = (x1 + x3) / 2;
		y1 = (y1 + y3) / 2;
		x3 = x1 + (x3 - x1) * dd / dmx;
		y3 = y1 + (y3 - y1) * dd / dmx;

		var dd = Math.sqrt(distAB(x3, y3, x2, y2));
		var fx = x2 + (x3 - x2) * ndRad / dd;	
		var fy = y2 + (y3 - y2) * ndRad / dd;
		var sx = x2 + (x3 - x2) * (ndRad + dirTriLen) / dd;
		var sy = y2 + (y3 - y2) * (ndRad + dirTriLen) / dd;

		var trg = new Object(), dis = dirTriLen / 2;
		if (sx == fx) {
			trg.t1X = sx + dis;
			trg.t1Y = sy;
			trg.t2X = sx - dis;
			trg.t2Y = sy;	
		} else if (sy == fy) {
			trg.t1X = sx;
			trg.t1Y = sy - dis;
			trg.t2X = sx;
			trg.t2Y = sy + dis;
		} else {
			var a0 = (sy - fy) / (sx - fx), b0 = sy - a0 * sx;
			var trg = edgeArcTarget(sx, sy, a0, b0, dis); 
		}
		ctx.fillStyle = "Black";
		ctx.beginPath();
		ctx.moveTo(fx, fy);
		ctx.lineTo(trg.t1X, trg.t1Y);
		ctx.lineTo(trg.t2X, trg.t2Y);
		ctx.closePath();
		ctx.fill();
	}
}

function distToLine(x, y, a0, b0, x0, y0, x1, y1) {
	if (a0 == "nu") {
		if (y >= Math.min(y0, y1) && y <= Math.max(y0, y1)) {
			return Math.abs(x - x0);	
		}
		return maxInt;
	} else if (Math.abs(a0) < zeroLimit) {
		if (x >= Math.min(x0, x1) && x <= Math.max(x0, x1)) {
			return Math.abs(y - y0);	
		}
		return maxInt;
	}
	var	a1 = -1 / a0, b1 = y - a1 * x;
	var x2 = (b1 - b0) / (a0 - a1), y2 = a1 * x2 + b1;	

	if (x2 < Math.min(x0, x1) || x2 > Math.max(x0, x1))
		return maxInt;
	if (y2 < Math.min(y0, y1) || y2 > Math.max(y0, y1))
		return maxInt;
	return Math.sqrt(distAB(x, y, x2, y2));
}

function calcEdge(i) {
	var x0 = nodes[mapNd[edges[i].first]].posX;
	var y0 = nodes[mapNd[edges[i].first]].posY;
	var x1 = nodes[mapNd[edges[i].second]].posX;
	var y1 = nodes[mapNd[edges[i].second]].posY;
	var mx = (x0 + x1) / 2, my = (y0 + y1) / 2;
	if (x0 > x1) {
		var c = x0, x0 = x1, x1 = c;
		c = y0, y0 = y1, y1 = c;
	}
	if (x1 != x0) {
		var a0 = (y1 - y0) / (x1 - x0);
		var b0 = y0 - x0 * a0;	
	} else {
		var a0 = "nu";
		var b0 = "nu";
	}
	var minD = maxInt, id = -1;
	for (var j = 0; j < nodeCnt; j++) {
		if (j == mapNd[edges[i].first])	continue;
		if (j == mapNd[edges[i].second]) continue;

		var dd = distToLine(nodes[j].posX, nodes[j].posY, a0, b0, x0, y0, x1, y1);	
		if (dd < minD) {
			minD = dd;
			id = j;	
		}
	}
	var trg = edgeArcTarget(mx, my, a0, b0, 2 * ndRad + 2 * edDistErr);

	if (edges[i].arc != 0) {
		var d1 = distAB(edges[i].trdX, edges[i].trdY, trg.t1X, trg.t1Y);
		var d2 = distAB(edges[i].trdX, edges[i].trdY, trg.t2X, trg.t2Y);
		if (d1 <= d2)	edges[i].arc = 1;
		else	edges[i].arc = 2;	
	}
	if (minD < ndRad + edDistErr && id != -1) {
		if (edges[i].prc == 0) {
			d1 = distAB(nodes[id].posX, nodes[id].posY, trg.t1X, trg.t1Y);
			d2 = distAB(nodes[id].posX, nodes[id].posY, trg.t2X, trg.t2Y);
			edges[i].arc = (d1 <= d2) ? 2 : 1;	
		}
	} else {
		if (edges[i].prc == 1)	edges[i].arc = 0;
	}
	if (edges[i].arc == 0) {
		if (edges[i].prc > 0)	edges[i].prc -= edgePrcIncr;
		if (edges[i].prc < 0)	edges[i].prc = 0;
	} else {
		if (edges[i].prc < 1)	edges[i].prc += edgePrcIncr;
		if (edges[i].prc > 1)	edges[i].prc = 1;	
	}
	var tX, tY;	
	if (edges[i].arc == 0) {
		var d1 = distAB(edges[i].trdX, edges[i].trdY, trg.t1X, trg.t1Y);
		var d2 = distAB(edges[i].trdX, edges[i].trdY, trg.t2X, trg.t2Y);
		if (d1 < d2) {
			tX = trg.t1X;
			tY = trg.t1Y;	
		} else {
			tX = trg.t2X;
			tY = trg.t2Y;
		}
	}
	else if (edges[i].arc == 1) {
		tX = trg.t1X;
		tY = trg.t1Y;
	} else {
		tX = trg.t2X;
		tY = trg.t2Y;
	}
	edges[i].trdX = mx + edges[i].prc * (tX - mx);
	edges[i].trdY = my + edges[i].prc * (tY - my);
}


function fixAll() {
	for (var i = 0; i < nodeCnt; i++) {
		nodes[i].fix = 1;
	}
}
function unfixAll() {
	for (var i = 0; i < nodeCnt; i++) {
		nodes[i].fix = 0;
	}
}

function hideInpBox() {
	for (var i = 0; i < nodeCnt; i++) {
		if (nodes[i].type == 1) {
			nodes[i].type = 0;
			if (inpBox.value.length > 0) {
				for (var j = 0; j < edgeCnt; j++) {
					if (edges[j].first == nodes[i].name)	edges[j].first = inpBox.value;
					if (edges[j].second == nodes[i].name)	edges[j].second = inpBox.value;
				}
				nodes[i].name = inpBox.value;
				mapNd[nodes[i].name] = i;
			}
		}
	}
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].type == 1) {
			edges[i].type = 0;
			edges[i].leng = inpBox.value;
			if (edges[i].leng > maxLeng)	edges[i].leng = maxLeng;
			if (edges[i].leng < -maxLeng)	edges[i].leng = -maxLeng;
			if (!isNumeric(edges[i].leng))	edges[i].leng = "";
		}
	}
	inpBox.className = "canvasInput hidden";	
	graphInputUpdate();
}

function hitEnterEsc(event) {
	if (event.keyCode == 13 || event.keyCode == 27) {
		if (graphMode == "edit") {
			hideInpBox();
		}
	}
}

function mouseDown() {
	time = 0;
	if (pathMode) {
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 1;
				return;
			}
		return;
	}
	if (graphMode == "gravity") {
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 1;
				return;
			}
		return;
	}
	if (graphMode == "edit") {
		hideInpBox();
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 1;
				return;
			}
		return;
	}
	if (graphMode == "draw") {
		for (var i = 0; i < nodeCnt; i++)
			if (drwId == -1 && distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 1;
				return;	
			}
	}
	if (graphMode == "delete") {
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 1;
				return;	
			}
	}
}

function mouseUp() {
  //console.log("AM FACUT UN CLICK   TIMPUL: " + time);
	if (pathMode) {
		for (var i = 0; i < nodeCnt; i++)	
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 0;
				if (time < clickTime) {
					if (seen[i])	return;
					if (pathAlg == "DFS") {
						DFS(i, -1);
						startAnimatePath();
						return;
					}
					if (pathAlg == "BFS") {
						BFS(i, -1);
						startAnimatePath();
						return;
					}
					if (pathAlg == "DJK") {
						DJK(i);
						startAnimatePath();
					}
					if (pathAlg == "MF") {
						if (sMF == -1)	sMF = i;
						else if (fMF == -1 && i != sMF) {
							fMF = i;
							MF(sMF, fMF);
						}
					}
				}
			}
		return;
	}
	if (graphMode == "gravity") {
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 0;
				if (time < clickTime) {
					if (nodes[i].fix == 0)	nodes[i].fix = 1;
					else if (nodes[i].fix == 1)	nodes[i].fix = 0;
				}
				return;
			}
		return;
	}
	if (graphMode == "edit") {
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 0;			
				if (time < clickTime) {
					nodes[i].type = 1;
					inpBox.className = "canvasInput";
					inpBox.value = nodes[i].name;
					updateInputBox(nodes[i].posX, nodes[i].posY);
					graphInputUpdate();
					inpBox.focus();
					inpBox.select();
				}
				return;
			}
		for (var i = 0; i < edgeCnt; i++) {
			if (edges[i].second == undefined || edges[i].second.length == 0)	continue;
			if (distPointEdge(mX, mY, i) < clickEdgeDist) {
				if (time < clickTime) {
					edges[i].type = 1;
					inpBox.className = "canvasInput";
					if (edges[i].leng != undefined) {
						inpBox.value = edges[i].leng;
						graphInputUpdate();
					} else {
						inpBox.value = "0";
						graphInputUpdate();
					}
					if (edges[i].lengX != undefined && edges[i].lengX != 0) {
						updateInputBox(edges[i].lengX, edges[i].lengY);
					}
					inpBox.focus();
					inpBox.select();
				}
			}
		}
		return;
	}
	if (graphMode == "draw") {
		for (var i = 0; i < nodeCnt; i++)
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 0;
				if (time < clickTime) {
					if (drwId != -1 && drwId != i) {
						edges[edgeCnt] = new Object();
						edges[edgeCnt].prc = 0;
						edges[edgeCnt].arc = 0;
						edges[edgeCnt].trdX = 0;
						edges[edgeCnt].trdY = 0;
						edges[edgeCnt].type = 0;
						edges[edgeCnt].leng = "";
						edges[edgeCnt].color = "black";
						edges[edgeCnt].first = nodes[drwId].name;
						edges[edgeCnt].second = nodes[i].name;	
						edgeCnt++;
						graphInputUpdate();	
						drwId = -1;
					}
					else if (drwId == -1) {
						drwX = nodes[i].posX;
						drwY = nodes[i].posY;	
						drwId = i;
					}
				}
				return;
			}

		if (time < clickTime && drwId == -1 && mX >= ndRad && mX + ndRad <= cnvSz && mY >= ndRad && mY + ndRad <= cnvSz) {
			nodes[nodeCnt] = new Object();
			nodes[nodeCnt].name = String(nextIntNumb());	
			mapNd[nodes[nodeCnt].name] = nodeCnt;
			nodes[nodeCnt].posX = mX;
			nodes[nodeCnt].posY = mY;
			nodes[nodeCnt].vX = 0;
			nodes[nodeCnt].vY = 0;
			nodes[nodeCnt].grab = 0;
			nodes[nodeCnt].type = 0;
			nodes[nodeCnt].fix = 0;
			nodes[nodeCnt].color = "black";
			console.log("AM CREAT: " + nodeCnt);
			nodeCnt++;
			edges[edgeCnt] = new Object();
			edges[edgeCnt].first = nodes[nodeCnt - 1].name;
			edges[edgeCnt].second = "";
			edges[edgeCnt].leng = "";
			edges[edgeCnt].arc = 0;
			edges[edgeCnt].prc = 0;
			edges[edgeCnt].trdX = 0;
			edges[edgeCnt].trdY = 0;
			edges[edgeCnt].type = 0;
			edges[edgeCnt].color = "black";
			edgeCnt++;
			graphInputUpdate();
		}
		drwId = -1;
	}
	if (graphMode == "delete") {
		for (var i = 0; i < nodeCnt; i++) {
			if (distAB(mX, mY, nodes[i].posX, nodes[i].posY) < ndRad * ndRad) {
				nodes[i].grab = 0;
				if (time < clickTime) {
					deleteNode(i);
					graphInputUpdate();
				}
				return;
			}
		}
		for (var i = 0; i < edgeCnt; i++) {
			if (edges[i].second == undefined || edges[i].second.length == 0)	continue;
			if (distPointEdge(mX, mY, i) < clickEdgeDist) {
				if (time < clickTime) {
					deleteEdge(i);
					graphInputUpdate();
				}
				return;
			}
		}
	}
} 

function mouseLeaveCnv() {
	time = clickTime;
	mouseUp();
	var dd = $("#inputBox").is(":hover");
	if (graphMode == "edit" && !dd) hideInpBox();
	if (graphMode == "draw")	drwId = -1;
}

function forceNC(i) {
	var d = distAB(nodes[i].posX, nodes[i].posY, cx, cy);
	var dx = Math.abs(nodes[i].posX - cx);
	var dy = Math.abs(nodes[i].posY - cy);

	if (d == 0)	d = 10;
	var ax = Math.sqrt(d) * ncF;

	if (dx) {
		var m = Math.abs((nodes[i].posY - cy) / (nodes[i].posX - cx));
		var c = Math.sqrt(ax * ax / (m * m + 1));
		nodes[i].vX += c * (nodes[i].posX < cx ? 1 : -1);  
		nodes[i].vY += m * c * (nodes[i].posY < cy ? 1 : -1);
	} else {
		nodes[i].vY += ax * (nodes[i].posY < cy ? 1 : -1);
	}
}

function forceNN(i, j) { 	
	var d = distAB(nodes[i].posX, nodes[i].posY, nodes[j].posX, nodes[j].posY);	
	var dx = Math.abs(nodes[i].posX - nodes[j].posX);
	var dy = Math.abs(nodes[i].posY - nodes[j].posY);
	
	if (d == 0) {
		nodes[i].vX += -5 + Math.random() * 10;	
		nodes[i].vY += -5 + Math.random() * 10;	
		return;
	}
	var ax = ndRad * ndRad * nnF / d / d;

	if (dx) {
		var m = Math.abs((nodes[i].posY - nodes[j].posY) / (nodes[i].posX - nodes[j].posX)); 
		var c = Math.sqrt(ax * ax / (m * m + 1));
		nodes[i].vX += c * -(nodes[i].posX < nodes[j].posX ? 1 : -1);
		nodes[i].vY += m * c * -(nodes[i].posY < nodes[j].posY ? 1 : -1);
	} else {
		nodes[i].vY += ax * -(nodes[i].posY < nodes[j].posY ? 1 : -1);
	}
}

function forceEd(i, j) {
	var d = distAB(nodes[i].posX, nodes[i].posY, nodes[j].posX, nodes[j].posY);	
	var dx = Math.abs(nodes[i].posX - nodes[j].posX);
	
	var ddif = d - edgeIdealLength * edgeIdealLength;
	if (ddif == 0)	d = 1;

	var ax = edF * Math.sqrt(Math.abs(ddif));
	var sg = (ddif > 0 ? 1 : -1);

	if (dx) {
		var m = Math.abs((nodes[i].posY - nodes[j].posY) / (nodes[i].posX - nodes[j].posX));
		var c = Math.sqrt(ax * ax / (m * m + 1));
		nodes[i].vX += sg * c * (nodes[i].posX < nodes[j].posX ? 1 : -1);
		nodes[i].vY += sg * m * c * (nodes[i].posY < nodes[j].posY ? 1 : -1);
	} else {
		nodes[i].vY += sg * ax * (nodes[i].posY < nodes[j].posY ? 1 : -1);
	}
}

function checkGoAnim() {
	for (var i = 0; i < nodeCnt; i++) {
		var dd = distAB(0, 0, nodes[i].vX, nodes[i].vY); 
		if (dd > fErr) {
			return true;
		}
	}
	return false;
}

function updateNodePos(i) {
	if (nodes[i].grab == 0 && graphMode == "edit")	return;
	if (nodes[i].grab == 0 && graphMode == "draw")	return;
	if (nodes[i].grab == 0 && graphMode == "delete")	return;
	if (nodes[i].grab == 1) {
		nodes[i].posX = mX;
		nodes[i].posY = mY;
	}
	else if (nodes[i].fix == 0) {
		nodes[i].posX += +nodes[i].vX;
		nodes[i].posY += +nodes[i].vY;
	}
	if (nodes[i].posX > cnvSz - ndRad)	{
		nodes[i].posX = cnvSz - ndRad;
		nodes[i].vX = 0;
	}
	if (nodes[i].posY > cnvSz - ndRad) {
		nodes[i].posY = cnvSz - ndRad;
		nodes[i].vY = 0;
	}
	if (nodes[i].posX < ndRad) {
		nodes[i].posX = ndRad;
		nodes[i].vX = 0;
	}
	if (nodes[i].posY < ndRad) {
		nodes[i].posY = ndRad;
		nodes[i].vY = 0;
	}
}

function calcNodeVect() {
	for (var i = 0; i < nodeCnt; i++) {
		forceNC(i);
		for (var j = 0; j < nodeCnt; j++)
			if (i != j) {
				forceNN(i, j);
			}
	}
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].second == undefined || edges[i].second.length == 0)	continue;
		forceEd(mapNd[edges[i].first], mapNd[edges[i].second]); 			
		forceEd(mapNd[edges[i].second], mapNd[edges[i].first]); 			
	}
	for (var i = 0; i < nodeCnt; i++) {
		nodes[i].vX *= dragRate;
		nodes[i].vY *= dragRate;
	
		if (Math.abs(nodes[i].vX) > maxVel || Math.abs(nodes[i].vY) > maxVel) {
			var m = maxVel / Math.max(Math.abs(nodes[i].vX), Math.abs(nodes[i].vY));
			nodes[i].vX *= m;
			nodes[i].vY *= m;	
		}
	}
}

function drawGraph() {
	ctx.clearRect(0, 0, cnv.width, cnv.height);	
	ctx.font = "30px Monospace";
	ctx.textAlign = "center";
	ctx.textBaseline = "middle";	
	ctx.lineWidth = lineWidth;	
	
	if (drwId != -1) {
		ctx.beginPath();
		ctx.moveTo(drwX, drwY);
		ctx.lineTo(mX, mY);
		ctx.strokeStyle = "black";
		ctx.stroke();
	}
	for (var i = 0; i < edgeCnt; i++) {
		if (edges[i].second == undefined || edges[i].second.length == 0)	continue;
		calcEdge(i);
		var x0 = nodes[mapNd[edges[i].first]].posX;
		var y0 = nodes[mapNd[edges[i].first]].posY;
		var x1 = nodes[mapNd[edges[i].second]].posX;
		var y1 = nodes[mapNd[edges[i].second]].posY;
		drawEdgeArc(i, x0, y0, edges[i].trdX, edges[i].trdY, x1, y1);
	}
	ctx.font = "30px Monospace";
	ctx.textAlign = "center";
	ctx.textBaseline = "middle";	

	for (var i = 0; i < nodeCnt; i++) {
		ctx.lineWidth = arcLineWidth;
		if (nodes[i].fix == 1)	ctx.lineWidth = thickArcLineWidth;
		
		ctx.beginPath();
		ctx.arc(nodes[i].posX, nodes[i].posY, ndRad, 0, 2 * Math.PI);	
		ctx.strokeStyle = nodes[i].color;
		ctx.stroke();	
		var str = document.getElementById("nodeBackColor").value;
		ctx.fillStyle = str;
		ctx.fill();
		if (nodes[i].type == 0) {
			ctx.fillStyle = document.getElementById("nodeColor").value;
			ctx.fillText(nodes[i].name, nodes[i].posX, nodes[i].posY);
		}
		if (nodes[i].type == 1) {
			updateInputBox(nodes[i].posX, nodes[i].posY);
		}
	}
}

function startAnimate() {
	fpsInterval = 1000 / FPS;
	then = Date.now();
	animate();
}

function animate() {
	//if (!checkGoAnim() && ct > 1)	return; 
	requestAnimationFrame(animate);
	
	now = Date.now();
	elapsed = now - then;

	if (elapsed > fpsInterval) {
		then = now - (elapsed % fpsInterval);
			
		if (graphMode == "gravity")
			calcNodeVect();
		ct++;
  	console.log("end " + edgeCnt);
		for (var i = 0; i < nodeCnt; i++) {
			updateNodePos(i);
		}
		drawGraph();
	}
}

function addNode(id) {
	console.log("addNode " + id);
	if (nodes[id] == undefined) { 
		nodes[id] = new Object();
		nodes[id].posX = Math.random() * cnvSz;
		nodes[id].posY = Math.random() * cnvSz;
	}
	nodes[id].vX = 0;
	nodes[id].vY = 0;	
}

function updateGraphData() {
	console.log("updateGraphData");
	resetPlayer();
	var txt = document.getElementById("graphData").value;
	var textA = document.getElementById("graphData");

	newEdges = [];
	newNodes = [];
	mapNd = {};

	var eC = 0, nC = 0, nrCnt = 0, str = "";
	newEdges[eC] = new Object();	
	for (var i = 0; i < txt.length; i++) {
		if (txt[i] != ' ' && txt[i] != '\n') {
			str += txt[i];
		}
		if (txt[i] == ' ' || i + 1 == txt.length || txt[i] == '\n') {
			if (str.length) {
				nrCnt++;
				if (nrCnt == 1) {
					newEdges[eC].first = str;
				}
				if (nrCnt == 2) {
					newEdges[eC].second = str;
				}
				if (nrCnt == 3) {
					newEdges[eC].leng = str;
					if (newEdges[eC].leng > maxLeng)	newEdges[eC].leng = maxLeng;
					if (newEdges[eC].leng < -maxLeng)	newEdges[eC].leng = -maxLeng;
				}
				if (nrCnt <= 2 && mapNd[str] == undefined) {
					mapNd[str] = nC;
					newNodes[nC] = str;
					nC++;
				}
				str = "";
			}
			if ((txt[i] == '\n' || i + 1 == txt.length) && nrCnt) {
				eC++;
				newEdges[eC] = new Object();
				nrCnt = 0;
			}
		}
	}
	if (newEdges[eC].first != undefined)	eC++;
	
	//console.log("nodeCnt " + nodeCnt);
	//console.log("nodeCnt " + nC);
	var k = 0;
	for (var i = 0; i < nodeCnt; i++) {
		var ok = 0;
		for (var j = 0; j < nC; j++)
			if (nodes[i].name == newNodes[j]) {
				ok = 1;
				break;
			}
		if (ok) {
			swapNodes(k, i);
			k++;
		}
	}
	for (var i = 0; i < nC; i++) {
		var ok = 0;
		for (var j = 0; j < nodeCnt; j++)
			if (newNodes[i] == nodes[j].name) {
				ok = 1;
				break;
			}
		if (!ok) {
			addNode(k);
			nodes[k].name = newNodes[i];
			k++;	
		}
	}
	var sumCh = 0;
	for (var i = 0; i < eC; i++) {
		if (edges[i] == undefined)	edges[i] = new Object();
		edges[i].first = newEdges[i].first;
		edges[i].second = newEdges[i].second;
		edges[i].leng = newEdges[i].leng;
		if (edges[i].leng == undefined)	edges[i].leng = "";
		edges[i].type = 0;
		if (edges[i].arc == undefined)	edges[i].arc = 0;
		if (edges[i].prc == undefined)	edges[i].prc = 0;
		if (edges[i].trdX == undefined)	edges[i].trdX = 0;
		if (edges[i].trdY == undefined)	edges[i].trdY = 0;
		edges[i].color = "black";
	
		if (edges[i].first != undefined)	sumCh += edges[i].first.length + 1;
		if (edges[i].second != undefined)	sumCh += edges[i].second.length + 1;
		if (edges[i].leng != undefined)	sumCh += edges[i].leng.length + 1;

		if (edges[i].leng.length > 0 && !isNumeric(edges[i].leng)) {
			var ll = edges[i].leng.length;
			edges[i].leng = "";
			graphInputUpdate();
			textA.focus();
			textA.selectionEnd = sumCh - ll - 1;
		}
	}
	for (var i = 0; i < nC; i++) {
		nodes[i].vX = 0;
		nodes[i].vY = 0;
		nodes[i].grab = 0;
		nodes[i].type = 0;
		mapNd[nodes[i].name] = i;
		if (nodes[i].fix == undefined)	nodes[i].fix = 0;
		if (nodes[i].color == undefined)	nodes[i].color = "black";
	}
	if (nodeCnt > nC) {
		for (var i = nC; i < nodeCnt; i++) {
			nodes[i].fix = 0;
		}
	}
	if (edgeCnt > eC) {
		for (var i = eC; i < edgeCnt; i++) {
			edges[i].prc = 0;
			edges[i].arc = 0;
			edges[i].trdX = 0;
			edges[i].trdY = 0;
			edges[i].type = 0;
			edges[i].leng = "";
			edges[i].color = "black";
		}
	}
	nodeCnt = nC;
	edgeCnt = eC;
	
	//console.log("am modificat datele grafului");	
	//console.log("noduri si mucii \n");
	//console.log(nodeCnt + '\n');	
	//console.log(edgeCnt + '\n');	
	//console.log("hsi sa vedem muchiiile");
	//for (var i = 0; i < edgeCnt; i++) {
		//console.log(edges[i].first + ' ' + edges[i].second + ' ' + edges[i].leng);	
	//} 
	//console.log("hai sa vedem nodurile");
	//for (var i = 0; i < nodeCnt; i++) {
		//console.log(nodes[i].name + " " + nodes[i].posX + " " + nodes[i].posY + " " + nodes[i].vX + " " + nodes[i].vY);
	//}
	document.getElementById("nodeCount").value = nodeCnt;

	ct = 0;
	console.log("started animation");
	startAnimate();
	
	checkCycle();
	checkIsLenght();
	
	console.log("END updateGraphData");
}

function updateNodeSize() {
	var str = document.getElementById("nodeSize").value;	
	if (isNumber(str) && str.length > 0)
		ndRad = str;
	if (ndRad > cnvSz / 2)
		ndRad = cnvSz / 2;
	if (ndRad > maxNodeRad)
		ndRad = maxNodeRad;
	if (ndRad <= 0)
		ndRad = 1;
	if (str.length > 0)
		document.getElementById("nodeSize").value = ndRad;
	
	ndRad *= 1;
	drawGraph();
}

function updateEdgeIdealLength() {
	var str = document.getElementById("edgeLength").value;

	if (isNumber(str))
		edgeIdealLength = str;
	if (edgeIdealLength > cnvSz && str.length > 0)
		edgeIdealLength = cnvSz;
	if (edgeIdealLength <= 0)
		edgesIdealLength = 1;
	if (str.length > 0)
		document.getElementById("edgeLength").value = edgeIdealLength;
	
	edgeIdealLength *= 1;
	drawGraph();
}

function hideAllTabs() {
	document.getElementById("gravityTab").className = "gravityTab hidden";
	document.getElementById("editTab").className = "editTab hidden";
	document.getElementById("inputBox").className = "canvasInput hidden";
	document.getElementById("drawTab").className = "drawTab hidden";
	document.getElementById("deleteTab").className = "deleteTab hidden";	
	document.getElementById("pathTab").className = "pathTab hidden";
	document.getElementById("highlightTab").className = "highlightTab hidden";
	document.getElementById("sortTab").className = "sortTab hidden";
	document.getElementById("configTab").className = "configTab hidden";
}
function selectPaths() {
	pathMode = 1;
	pathHigh = 0;
	hideAllTabs();
	document.getElementById("pathTab").className = "pathTab";
}
function selectHighLight() {
	pathMode = 0;
	pathHigh = 1;
	hideAllTabs();
	document.getElementById("highlightTab").className = "highlightTab";
}
function selectSort() {
	pathMode = 0;
	pathHigh = 0;
	hideAllTabs();
	document.getElementById("sortTab").className = "sortTab";
}
function selectConfig() {
	pathMode = 0;
	pathHigh = 0;
	hideAllTabs();
	document.getElementById("configTab").className = "configTab";
}
function selectGravity() {
	pathMode = 0;
	pathHigh = 0;
	graphMode = "gravity";
	hideAllTabs();
	document.getElementById("gravityTab").className = "gravityTab";
}
function selectEdit() {
	pathMode = 0;
	pathHigh = 0;
	graphMode = "edit";
	hideAllTabs();
	document.getElementById("editTab").className = "editTab";
	inpBox = document.getElementById("inputBox");
}
function selectDraw() {
	pathMode = 0;
	pathHigh = 0;
	graphMode = "draw";
	hideAllTabs();
	document.getElementById("drawTab").className = "drawTab";
}
function selectDelete() {
	pathMode = 0;
	pathHigh = 0;
	graphMode = "delete";
	hideAllTabs();
	document.getElementById("deleteTab").className = "deleteTab";
}
