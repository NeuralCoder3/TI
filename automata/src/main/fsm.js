var greekLetterNames = [ 'Alpha', 'Beta', 'Gamma', 'Delta', 'Epsilon', 'Zeta', 'Eta', 'Theta', 'Iota', 'Kappa', 'Lambda', 'Mu', 'Nu', 'Xi', 'Omicron', 'Pi', 'Rho', 'Sigma', 'Tau', 'Upsilon', 'Phi', 'Chi', 'Psi', 'Omega' ];

function convertLatexShortcuts(text) {
	// html greek characters
	for(var i = 0; i < greekLetterNames.length; i++) {
		var name = greekLetterNames[i];
		text = text.replace(new RegExp('\\\\' + name, 'g'), String.fromCharCode(913 + i + (i > 16)));
		text = text.replace(new RegExp('\\\\' + name.toLowerCase(), 'g'), String.fromCharCode(945 + i + (i > 16)));
	}

	// subscripts
	for(var i = 0; i < 10; i++) {
		text = text.replace(new RegExp('_' + i, 'g'), String.fromCharCode(8320 + i));
	}

	return text;
}

function textToXML(text) {
	text = text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
	var result = '';
	for(var i = 0; i < text.length; i++) {
		var c = text.charCodeAt(i);
		if(c >= 0x20 && c <= 0x7E) {
			result += text[i];
		} else {
			result += '&#' + c + ';';
		}
	}
	return result;
}

function drawArrow(c, x, y, angle) {
	var dx = Math.cos(angle);
	var dy = Math.sin(angle);
	c.beginPath();
	c.moveTo(x, y);
	c.lineTo(x - 8 * dx + 5 * dy, y - 8 * dy - 5 * dx);
	c.lineTo(x - 8 * dx - 5 * dy, y - 8 * dy + 5 * dx);
	c.fill();
}

function canvasHasFocus() {
	return (document.activeElement || document.body) == document.body;
}

function drawText(c, originalText, x, y, angleOrNull, isSelected) {
	text = convertLatexShortcuts(originalText);
	c.font = '20px "Times New Roman", serif';
	var width = c.measureText(text).width;

	// center the text
	x -= width / 2;

	// position the text intelligently if given an angle
	if(angleOrNull != null) {
		var cos = Math.cos(angleOrNull);
		var sin = Math.sin(angleOrNull);
		var cornerPointX = (width / 2 + 5) * (cos > 0 ? 1 : -1);
		var cornerPointY = (10 + 5) * (sin > 0 ? 1 : -1);
		var slide = sin * Math.pow(Math.abs(sin), 40) * cornerPointX - cos * Math.pow(Math.abs(cos), 10) * cornerPointY;
		x += cornerPointX - sin * slide;
		y += cornerPointY + cos * slide;
	}

	// draw text and caret (round the coordinates so the caret falls on a pixel)
	if('advancedFillText' in c) {
		c.advancedFillText(text, originalText, x + width / 2, y, angleOrNull);
	} else {
		x = Math.round(x);
		y = Math.round(y);
		c.fillText(text, x, y + 6);
		if(isSelected && caretVisible && canvasHasFocus() && document.hasFocus()) {
			x += width;
			c.beginPath();
			c.moveTo(x, y - 10);
			c.lineTo(x, y + 10);
			c.stroke();
		}
	}
}

var caretTimer;
var caretVisible = true;

function resetCaret() {
	clearInterval(caretTimer);
	caretTimer = setInterval('caretVisible = !caretVisible; draw()', 500);
	caretVisible = true;
}

var canvas;
var nodeRadius = 30;
var nodes = [];
var links = [];

var cursorVisible = true;
var snapToPadding = 6; // pixels
var hitTargetPadding = 6; // pixels
var selectedObject = null; // either a Link or a Node
var currentLink = null; // a Link
var movingObject = false;
var originalClick;

function drawUsing(c) {
	c.clearRect(0, 0, canvas.width, canvas.height);
	c.save();
	c.translate(0.5, 0.5);

	for(var i = 0; i < nodes.length; i++) {
		c.lineWidth = 1;
		c.fillStyle = c.strokeStyle = (nodes[i] == selectedObject) ? 'blue' : 'black';
		nodes[i].draw(c);
	}
	for(var i = 0; i < links.length; i++) {
		c.lineWidth = 1;
		c.fillStyle = c.strokeStyle = (links[i] == selectedObject) ? 'blue' : 'black';
		links[i].draw(c);
	}
	if(currentLink != null) {
		c.lineWidth = 1;
		c.fillStyle = c.strokeStyle = 'black';
		currentLink.draw(c);
	}

	c.restore();
}

function draw() {
	drawUsing(canvas.getContext('2d'));
	saveBackup();
}

function selectObject(x, y) {
	for(var i = 0; i < nodes.length; i++) {
		if(nodes[i].containsPoint(x, y)) {
			return nodes[i];
		}
	}
	for(var i = 0; i < links.length; i++) {
		if(links[i].containsPoint(x, y)) {
			return links[i];
		}
	}
	return null;
}

function snapNode(node) {
	for(var i = 0; i < nodes.length; i++) {
		if(nodes[i] == node) continue;

		if(Math.abs(node.x - nodes[i].x) < snapToPadding) {
			node.x = nodes[i].x;
		}

		if(Math.abs(node.y - nodes[i].y) < snapToPadding) {
			node.y = nodes[i].y;
		}
	}
}

window.onload = function() {
	canvas = document.getElementById('canvas');
	restoreBackup();
	draw();

	canvas.onmousedown = function(e) {
		var mouse = crossBrowserRelativeMousePos(e);
		selectedObject = selectObject(mouse.x, mouse.y);
		movingObject = false;
		originalClick = mouse;

		if(selectedObject != null) {
			if(shift && selectedObject instanceof Node) {
				currentLink = new SelfLink(selectedObject, mouse);
			} else {
				movingObject = true;
				deltaMouseX = deltaMouseY = 0;
				if(selectedObject.setMouseStart) {
					selectedObject.setMouseStart(mouse.x, mouse.y);
				}
			}
			resetCaret();
		} else if(shift) {
			currentLink = new TemporaryLink(mouse, mouse);
		}

		draw();

		if(canvasHasFocus()) {
			// disable drag-and-drop only if the canvas is already focused
			return false;
		} else {
			// otherwise, let the browser switch the focus away from wherever it was
			resetCaret();
			return true;
		}
	};

	canvas.ondblclick = function(e) {
		var mouse = crossBrowserRelativeMousePos(e);
		selectedObject = selectObject(mouse.x, mouse.y);

		if(selectedObject == null) {
			selectedObject = new Node(mouse.x, mouse.y);
			nodes.push(selectedObject);
			resetCaret();
			draw();
		} else if(selectedObject instanceof Node) {
			selectedObject.isAcceptState = !selectedObject.isAcceptState;
			draw();
		}
	};

	canvas.onmousemove = function(e) {
		var mouse = crossBrowserRelativeMousePos(e);

		if(currentLink != null) {
			var targetNode = selectObject(mouse.x, mouse.y);
			if(!(targetNode instanceof Node)) {
				targetNode = null;
			}

			if(selectedObject == null) {
				if(targetNode != null) {
					currentLink = new StartLink(targetNode, originalClick);
				} else {
					currentLink = new TemporaryLink(originalClick, mouse);
				}
			} else {
				if(targetNode == selectedObject) {
					currentLink = new SelfLink(selectedObject, mouse);
				} else if(targetNode != null) {
					currentLink = new Link(selectedObject, targetNode);
				} else {
					currentLink = new TemporaryLink(selectedObject.closestPointOnCircle(mouse.x, mouse.y), mouse);
				}
			}
			draw();
		}

		if(movingObject) {
			selectedObject.setAnchorPoint(mouse.x, mouse.y);
			if(selectedObject instanceof Node) {
				snapNode(selectedObject);
			}
			draw();
		}
	};

	canvas.onmouseup = function(e) {
		movingObject = false;

		if(currentLink != null) {
			if(!(currentLink instanceof TemporaryLink)) {
				selectedObject = currentLink;
				links.push(currentLink);
				resetCaret();
			}
			currentLink = null;
			draw();
		}
	};
}

var shift = false;

document.onkeydown = function(e) {
	var key = crossBrowserKey(e);

	if(key == 16) {
		shift = true;
	} else if(!canvasHasFocus()) {
		// don't read keystrokes when other things have focus
		return true;
	} else if(key == 8) { // backspace key
		if(selectedObject != null && 'text' in selectedObject) {
			selectedObject.text = selectedObject.text.substr(0, selectedObject.text.length - 1);
			resetCaret();
			draw();
		}

		// backspace is a shortcut for the back button, but do NOT want to change pages
		return false;
	} else if(key == 46) { // delete key
		if(selectedObject != null) {
			for(var i = 0; i < nodes.length; i++) {
				if(nodes[i] == selectedObject) {
					nodes.splice(i--, 1);
				}
			}
			for(var i = 0; i < links.length; i++) {
				if(links[i] == selectedObject || links[i].node == selectedObject || links[i].nodeA == selectedObject || links[i].nodeB == selectedObject) {
					links.splice(i--, 1);
				}
			}
			selectedObject = null;
			draw();
		}
	}
};

document.onkeyup = function(e) {
	var key = crossBrowserKey(e);

	if(key == 16) {
		shift = false;
	}
};

document.onkeypress = function(e) {
	// don't read keystrokes when other things have focus
	var key = crossBrowserKey(e);
	if(!canvasHasFocus()) {
		// don't read keystrokes when other things have focus
		return true;
	} else if(key >= 0x20 && key <= 0x7E && !e.metaKey && !e.altKey && !e.ctrlKey && selectedObject != null && 'text' in selectedObject) {
		selectedObject.text += String.fromCharCode(key);
		resetCaret();
		draw();

		// don't let keys do their actions (like space scrolls down the page)
		return false;
	} else if(key == 8) {
		// backspace is a shortcut for the back button, but do NOT want to change pages
		return false;
	}
};

function crossBrowserKey(e) {
	e = e || window.event;
	return e.which || e.keyCode;
}

function crossBrowserElementPos(e) {
	e = e || window.event;
	var obj = e.target || e.srcElement;
	var x = 0, y = 0;
	while(obj.offsetParent) {
		x += obj.offsetLeft;
		y += obj.offsetTop;
		obj = obj.offsetParent;
	}
	return { 'x': x, 'y': y };
}

function crossBrowserMousePos(e) {
	e = e || window.event;
	return {
		'x': e.pageX || e.clientX + document.body.scrollLeft + document.documentElement.scrollLeft,
		'y': e.pageY || e.clientY + document.body.scrollTop + document.documentElement.scrollTop,
	};
}

function crossBrowserRelativeMousePos(e) {
	var element = crossBrowserElementPos(e);
	var mouse = crossBrowserMousePos(e);
	return {
		'x': mouse.x - element.x,
		'y': mouse.y - element.y
	};
}

function output(text) {
	var element = document.getElementById('output');
	element.style.display = 'block';
	element.value = text;
}

function saveAsPNG() {
	var oldSelectedObject = selectedObject;
	selectedObject = null;
	drawUsing(canvas.getContext('2d'));
	selectedObject = oldSelectedObject;
	var pngData = canvas.toDataURL('image/png');

  document.getElementById("overleafExport").style.display = "none";

  var iframe = "<iframe width='100%' height='100%' src='" + pngData + "'></iframe>"
  var x = window.open();
  x.document.open();
  x.document.write(iframe);
  x.document.close();

	// document.location.href = pngData;
}

function saveAsSVG() {
	var exporter = new ExportAsSVG();
	var oldSelectedObject = selectedObject;
	selectedObject = null;
	drawUsing(exporter);
	selectedObject = oldSelectedObject;
	var svgData = exporter.toSVG();
  document.getElementById("overleafExport").style.display="none";
	output(svgData);
	// Chrome isn't ready for this yet, the 'Save As' menu item is disabled
	// document.location.href = 'data:image/svg+xml;base64,' + btoa(svgData);
}

function saveAsLaTeX() {
	var exporter = new ExportAsLaTeX();
	var oldSelectedObject = selectedObject;
	selectedObject = null;
	drawUsing(exporter);
	selectedObject = oldSelectedObject;
	var texData = exporter.toLaTeX();
  document.getElementById("overleafExport").style.display="block";
	output(texData);
}

function simulateTuringDet() {
  var currentNode;
	for(var i = 0; i < nodes.length; i++) {
    if(nodes[i].text=="S"){
      currentNode=nodes[i];
    }
	}
  if(undefined === currentNode){
    alert("No starting node S found!");
  }
  var blank='0';
  var tapeLeft=[];
  var tapeRight=[blank];
  tapeRight=document.getElementById("tapeInput").value.split('');
  if(tapeRight.length==0){
    tapeRight=[blank];
  }
  var max=10000;
  var steps=0;
  var data="";
  while(steps<max || max<0) {
    found=false;
    for(var i = 0; i < links.length; i++) {
      var nodeA;
      var nodeB;
      var text;
      if(links[i] instanceof SelfLink){
        nodeA = links[i].node;
        nodeB = nodeA;
        text = links[i].text;
      }else if(links[i] instanceof Link){
        nodeA = links[i].nodeA;
        nodeB = links[i].nodeB;
        text = links[i].text;
      } else {
        continue;
      }
      parts=text.split(",");
      parts1=parts[0].split(";");
      read=parts1[0];
      write=parts1[1];
      direction=parts[1];
      if(nodeA!=currentNode)
        continue;
      if(read==tapeRight[0]){
        tapeRight[0]=write;
        move=direction.toLowerCase()[0];
        if(move=="r"){
          tapeLeft.unshift(tapeRight[0]);
          tapeRight.shift();
          if(tapeRight.length==0){
            tapeRight.unshift(blank);
          }
        }else if(move=="l"){
          if(tapeLeft.length==0){
            tapeLeft.unshift(blank);
          }
          tapeRight.unshift(tapeLeft[0]);
          tapeLeft.shift();
        }
        currentNode=nodeB;
        found=true;
        break;
      }
    }
    if(!found){
      break;
    }
    tape="";
    tapeLeftRev=tapeLeft.reverse();
    for(var i = 0; i < tapeLeftRev.length; i++) {
      tape+=tapeLeftRev[i];
    }
    for(var i = 0; i < tapeRight.length; i++) {
      if(i==0){
        tape+="<";
      }
      tape+=tapeRight[i];
      if(i==0){
        tape+=">";
      }
    }
    // console.log(tapeLeft);
    // console.log(tapeRight);
    steps+=1;
    data+="Step: "+i+"\n";
    data+=tape+"\n";
    // console.log("Step: "+i);
    // console.log(tape);
  }
  output(data);
  document.getElementById("overleafExport").style.display="none";
}

function simulateNFA() {
  var currentNode;
	for(var i = 0; i < nodes.length; i++) {
    if(nodes[i].text=="S"){
      currentNode=nodes[i];
    }
	}
  if(undefined === currentNode){
    alert("No starting node S found!");
  }
  var word=document.getElementById("tapeInput").value.split('');
  var currentNodes=[[word,currentNode]];
  var data="declined";
  out:
  while(true) {
    var newNodes=[]
    console.log(currentNodes);
    found=false;
    for(var j=0;j<currentNodes.length;j++){
      var word=currentNodes[j][0];
      var currentNode=currentNodes[j][1];
      if(word.length==0){
        console.log("empty in "+currentNode.text);
        if(currentNode.isAcceptState){
          console.log("accept");
          data="accepted";
          break out;
        }else {
          // data="declined";
        }
        // break;
      }
      for(var i = 0; i < links.length; i++) {
        var nodeA;
        var nodeB;
        var text;
        if(links[i] instanceof SelfLink){
          nodeA = links[i].node;
          nodeB = nodeA;
          text = links[i].text;
        }else if(links[i] instanceof Link){
          nodeA = links[i].nodeA;
          nodeB = links[i].nodeB;
          text = links[i].text;
        } else {
          continue;
        }
        if(nodeA!=currentNode)
          continue;
        found=true;
        if(text==word[0]){
          var word2=word.slice();
          word2.shift();
          newNodes.push([word2,nodeB]);
        }else if(text=="\\epsilon"){
          newNodes.push([word,nodeB]);
        }
      }
    }
    if(!found){
      break out;
    }
    currentNodes=newNodes;
  }
  output(data);
  document.getElementById("overleafExport").style.display="none";
}

function simulateDFA() {
  var currentNode;
	for(var i = 0; i < nodes.length; i++) {
    if(nodes[i].text=="S"){
      currentNode=nodes[i];
    }
	}
  if(undefined === currentNode){
    alert("No starting node S found!");
  }
  var word=document.getElementById("tapeInput").value.split('');
  var data="";
  while(true) {
    if(word.length==0){
      if(currentNode.isAcceptState){
        data="accepted";
      }else {
        data="declined";
      }
      break;
    }
    found=false;
    for(var i = 0; i < links.length; i++) {
      var nodeA;
      var nodeB;
      var text;
      if(links[i] instanceof SelfLink){
        nodeA = links[i].node;
        nodeB = nodeA;
        text = links[i].text;
      }else if(links[i] instanceof Link){
        nodeA = links[i].nodeA;
        nodeB = links[i].nodeB;
        text = links[i].text;
      } else {
        continue;
      }
      if(nodeA!=currentNode)
        continue;
      if(text==word[0]){
        word.shift();
        currentNode=nodeB;
        found=true;
        break;
      }
    }
    if(!found){
      data="declined";
      break;
    }
  }
  output(data);
  document.getElementById("overleafExport").style.display="none";
}

function saveAsText() {
  var data = "";
	for(var i = 0; i < nodes.length; i++) {
    data+=nodes[i].text+(nodes[i].isAcceptState ? ' (accepting)' : '')+"\n";
	}
	for(var i = 0; i < links.length; i++) {
    var textA="";
    var textB="";
    var textL="";
    // if(links[i] instanceof StartLink{
      // textA = "Start_"+links[i].node.text;
      // textB = textA;
      // textL = links[i].text;
    // }else 
    if(links[i] instanceof SelfLink){
      textA = links[i].node.text;
      textB = textA;
      textL = links[i].text;
    }else if(links[i] instanceof Link){
      textA = links[i].nodeA.text;
      textB = links[i].nodeB.text;
      textL = links[i].text;
    } else {
      continue;
    }
    data+=textA + " -> " + textB + " ("+textL+")" + "\n";
	}
  output(data);
}

function saveAsLaTeX2() {
	var exporter = new ExportAsLaTeX2();
	var oldSelectedObject = selectedObject;
	selectedObject = null;
	drawUsing(exporter);
	selectedObject = oldSelectedObject;
	var texData = exporter.toLaTeX2();
  document.getElementById("overleafExport").style.display="block";
	output(texData);
}
