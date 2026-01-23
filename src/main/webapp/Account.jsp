<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.service.StudenteService" %>
<%@ page import="it.unisa.uniclass.utenti.service.CoordinatoreService" %>
<%@ page import="it.unisa.uniclass.utenti.service.PersonaleTAService" %>
<%@ page import="it.unisa.uniclass.utenti.service.DocenteService" %>
<%@ page import="it.unisa.uniclass.utenti.model.*" %>

<%
    /* Sessione HTTP */
    HttpSession sessione = request.getSession(true);
    Utente user = (Utente) sessione.getAttribute("currentSessionUser");
    if(user != null){
        session.setAttribute("utenteEmail", user.getEmail());
    }

    StudenteService studenteService = new StudenteService();
    CoordinatoreService coordinatoreService = new CoordinatoreService();
    DocenteService docenteService = new DocenteService();
    PersonaleTAService personaleTAService = new PersonaleTAService();

    /* Variabili per visualizzazione unificata */
    String uNome = "";
    String uCognome = "";
    String uDataNascita = "";
    String uEmail = "";
    String uMatricolaOrId = "";
    String uCorsoOrTelefono = "";
    String uDataIscrizione = "";
    String userIcon = "images/icons/usericonnolog.png"; // Default

    /* Controllo tipo utente */
    Tipo tipoUtente = null;
    if (user != null) {
        tipoUtente = (Tipo) user.getTipo();
        uEmail = user.getEmail(); // Email è comune a tutti
    } else {
        response.sendRedirect("Login.jsp");
        return; // Importante per fermare l'esecuzione se redirect
    }

    /* Logica estrazione dati specifici */
    if(tipoUtente != null) {
        if (tipoUtente.equals(Tipo.Studente)) {
            Studente studente = studenteService.trovaStudenteEmailUniClass(user.getEmail());
            if (studente != null) {
                uNome = studente.getNome();
                uCognome = studente.getCognome();
                uDataNascita = "Data di nascita: " + studente.getDataNascita();
                uMatricolaOrId = studente.getMatricola();
                uCorsoOrTelefono = studente.getCorsoLaurea().getNome();
                uDataIscrizione = "Data di iscrizione: " + studente.getIscrizione();
                userIcon = "images/icons/iconstudent.png";
            }
        }
        else if (tipoUtente.equals(Tipo.Docente)) {
            Docente docente = docenteService.trovaEmailUniClass(user.getEmail());
            if (docente != null) {
                uNome = docente.getNome();
                uCognome = docente.getCognome();
                uDataNascita = "Data di nascita: " + docente.getDataNascita();
                uMatricolaOrId = docente.getMatricola();
                uCorsoOrTelefono = docente.getCorsoLaurea().getNome();
                uDataIscrizione = "Data di iscrizione: " + docente.getIscrizione();
                userIcon = "images/icons/iconprof.png";
            }
        }
        else if (tipoUtente.equals(Tipo.Coordinatore)) {
            Coordinatore coordinatore = coordinatoreService.trovaCoordinatoreEmailUniclass(user.getEmail());
            if (coordinatore != null) {
                uNome = coordinatore.getNome();
                uCognome = coordinatore.getCognome();
                uDataNascita = "Data di nascita: " + coordinatore.getDataNascita();
                uMatricolaOrId = coordinatore.getMatricola();
                uCorsoOrTelefono = coordinatore.getCorsoLaurea().getNome();
                uDataIscrizione = "Data di iscrizione alla piattaforma: " + coordinatore.getIscrizione();
                userIcon = "images/icons/iconprof.png";
            }
        }
        else if (tipoUtente.equals(Tipo.PersonaleTA)) {
            PersonaleTA personaleTA = personaleTAService.trovaEmail(user.getEmail());
            if (personaleTA != null) {
                uNome = personaleTA.getNome();
                uCognome = personaleTA.getCognome();
                uDataNascita = String.valueOf(personaleTA.getDataNascita());
                uMatricolaOrId = String.valueOf(personaleTA.getId());
                uCorsoOrTelefono = personaleTA.getTelefono();
                userIcon = "images/icons/iconpersonaleTA.png";
            }
        }
    }
%>

<!DOCTYPE html>
<html lang="it" xml:lang="it">

<head>
    <title>UniClass Account</title>
    <script src="scripts/sidebar.js" type="text/javascript"></script>
    <link type="text/css" rel="stylesheet" href="styles/headerStyle.css" />
    <link type="text/css" rel="stylesheet" href="styles/barraNavigazioneStyle.css"/>
    <link type="text/css" rel="stylesheet" href="styles/informazioniStyle.css">
    <link rel="icon" href="images/logois.png" sizes="32x32" type="image/png">
</head>

<body>

<div class="barraNavigazione" id="barraNavigazione">
    <a href="javascript:void(0)" class="closebtn" onclick="closeNav()">
        <img src="images/icons/menuOpenIcon.png" alt="closebtn">
    </a>
    <p>Menu</p>
    <ul id="menu">
        <li id="aule"><a href="aula.jsp">Aule</a></li>

        <%-- Logica Condizionale Menu: PersonaleTA vede Gestione Utenti, altri vedono Conversazioni --%>
        <% if(tipoUtente.equals(Tipo.PersonaleTA)) { %>
        <li id="gutenti"><a href="PersonaleTA/AttivaUtenti.jsp">Gestione Utenti</a></li>
        <% } else { %>
        <li id="conversazioni"><a href="Conversazioni">Conversazioni</a></li>
        <% } %>

        <li id="mappa"><a href="mappa.jsp">Mappa</a></li>
        <li id="ChatBot"><a href="ChatBot.jsp">ChatBot</a></li>
        <li id="infoapp"><a href="infoapp.jsp">Info App</a></li>
        <li id="aboutus"><a href="aboutus.jsp">Chi Siamo</a></li>
    </ul>
</div>

<jsp:include page="header.jsp" />

<div class="listaInfo" id="listaInfo">
    <h2>Informazioni</h2>
    <ul id="infolist">
        <img src="<%= userIcon %>" alt="immagineutente">

        <li id="nome"><%= uNome %></li>
        <li id="cognome"><%= uCognome %></li>
        <li id="dataNascita"><%= uDataNascita %></li>

        <%-- ID vs Matricola --%>
        <% if (tipoUtente.equals(Tipo.PersonaleTA)) { %>
        <li id="id"><%= uMatricolaOrId %></li>
        <% } else { %>
        <li id="matricola"><%= uMatricolaOrId %></li>
        <% } %>

        <li id="email"><%= uEmail %></li>

        <%-- Telefono vs Corso --%>
        <% if (tipoUtente.equals(Tipo.PersonaleTA)) { %>
        <li id="telefono"><%= uCorsoOrTelefono %></li>
        <% } else { %>
        <li id="corsoLaurea"><%= uCorsoOrTelefono %></li>
        <li id="dataIscrizione"><%= uDataIscrizione %></li>
        <% } %>
    </ul>

    <form action="LogoutServlet" method="post">
        <button type="submit" class="logout-button">Logout</button>
    </form>
</div>

</body>
</html>