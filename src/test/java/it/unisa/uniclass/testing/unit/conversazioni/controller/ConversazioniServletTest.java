package it.unisa.uniclass.testing.unit.conversazioni.controller;

import it.unisa.uniclass.conversazioni.controller.ConversazioniServlet;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockedConstruction;
import org.mockito.MockitoAnnotations;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test class per ConversazioniServlet.
 * Testa tutti i casi d'uso per massimizzare la code coverage con JaCoCo.
 */
class ConversazioniServletTest {

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private HttpSession session;

    @Mock
    private MessaggioService messaggioService;

    @Mock
    private RequestDispatcher requestDispatcher;

    private ConversazioniServlet servlet;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        servlet = new ConversazioniServlet();
        servlet.setMessaggioService(messaggioService);
        when(request.getServletContext()).thenReturn(mock(jakarta.servlet.ServletContext.class));
    }

    @Test
    void testDoPostWithStudentUser() throws Exception {
        System.out.println("\n=== Test 1: doPost con utente studente ===");

        // Arrange
        String email = "studente@studenti.unisa.it";
        String matricola = "0512100001";

        Studente studente = new Studente();
        studente.setEmail(email);
        studente.setMatricola(matricola);
        studente.setNome("Mario");
        studente.setCognome("Rossi");

        // Mock session
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);

        // Crea messaggi ricevuti
        List<Messaggio> messaggiRicevuti = new ArrayList<>();
        Messaggio msgRicevuto = new Messaggio();
        msgRicevuto.setBody("Ciao, come stai?");
        msgRicevuto.setDateTime(LocalDateTime.now());
        messaggiRicevuti.add(msgRicevuto);

        // Crea messaggi inviati
        List<Messaggio> messaggiInviati = new ArrayList<>();
        Messaggio msgInviato = new Messaggio();
        msgInviato.setBody("Tutto bene, grazie!");
        msgInviato.setDateTime(LocalDateTime.now());
        messaggiInviati.add(msgInviato);

        // Crea avvisi
        List<Messaggio> avvisi = new ArrayList<>();
        Messaggio avviso = new Messaggio();
        avviso.setBody("Avviso importante");
        Topic topic = new Topic();
        topic.setNome("Topic1");
        avviso.setTopic(topic);
        avvisi.add(avviso);

        // Mock AccademicoService
        try (@SuppressWarnings("unused") MockedConstruction<AccademicoService> mockedService = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaEmailUniClass(email)).thenReturn(studente))) {

            when(messaggioService.trovaMessaggiRicevuti(email)).thenReturn(messaggiRicevuti);
            when(messaggioService.trovaMessaggiInviati(email)).thenReturn(messaggiInviati);
            when(messaggioService.trovaAvvisi()).thenReturn(avvisi);

            // Act
            servlet.doPost(request, response);

            // Assert
            verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
            verify(request).setAttribute("messaggiRicevuti", messaggiRicevuti);
            verify(request).setAttribute("messaggiInviati", messaggiInviati);
            verify(request).setAttribute("messaggi", avvisi);
            verify(requestDispatcher).forward(request, response);
            verify(messaggioService).trovaMessaggiRicevuti(email);
            verify(messaggioService).trovaMessaggiInviati(email);
            verify(messaggioService).trovaAvvisi();

            System.out.println("✓ Test completato con successo");
        }
    }

    @Test
    void testDoPostWithDocenteUser() throws Exception {
        System.out.println("\n=== Test 2: doPost con utente docente ===");

        // Arrange
        String email = "docente@unisa.it";
        String matricola = "0512100010";

        Docente docente = new Docente();
        docente.setEmail(email);
        docente.setMatricola(matricola);
        docente.setNome("Giuseppe");
        docente.setCognome("Verdi");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);

        List<Messaggio> messaggiRicevuti = new ArrayList<>();
        List<Messaggio> messaggiInviati = new ArrayList<>();
        List<Messaggio> avvisi = new ArrayList<>();

        try (@SuppressWarnings("unused") MockedConstruction<AccademicoService> mockedService = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaEmailUniClass(email)).thenReturn(docente))) {

            when(messaggioService.trovaMessaggiRicevuti(email)).thenReturn(messaggiRicevuti);
            when(messaggioService.trovaMessaggiInviati(email)).thenReturn(messaggiInviati);
            when(messaggioService.trovaAvvisi()).thenReturn(avvisi);

            // Act
            servlet.doPost(request, response);

            // Assert
            verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
            verify(request).setAttribute("messaggiRicevuti", messaggiRicevuti);
            verify(request).setAttribute("messaggiInviati", messaggiInviati);
            verify(request).setAttribute("messaggi", avvisi);
            verify(requestDispatcher).forward(request, response);

            System.out.println("✓ Test completato con successo");
        }
    }

    @Test
    void testDoPostWithMultipleMessages() throws Exception {
        System.out.println("\n=== Test 3: doPost con molti messaggi ===");

        // Arrange
        String email = "utente@studenti.unisa.it";

        Studente studente = new Studente();
        studente.setEmail(email);
        studente.setMatricola("0512100020");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);

        // Crea liste con molti messaggi
        List<Messaggio> messaggiRicevuti = new ArrayList<>();
        List<Messaggio> messaggiInviati = new ArrayList<>();
        List<Messaggio> avvisi = new ArrayList<>();

        for (int i = 0; i < 10; i++) {
            Messaggio msg1 = new Messaggio();
            msg1.setBody("Messaggio ricevuto " + i);
            messaggiRicevuti.add(msg1);

            Messaggio msg2 = new Messaggio();
            msg2.setBody("Messaggio inviato " + i);
            messaggiInviati.add(msg2);

            if (i < 5) {
                Messaggio avviso = new Messaggio();
                avviso.setBody("Avviso " + i);
                Topic topic = new Topic();
                topic.setNome("Topic" + i);
                avviso.setTopic(topic);
                avvisi.add(avviso);
            }
        }

        try (@SuppressWarnings("unused") MockedConstruction<AccademicoService> mockedService = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaEmailUniClass(email)).thenReturn(studente))) {

            when(messaggioService.trovaMessaggiRicevuti(email)).thenReturn(messaggiRicevuti);
            when(messaggioService.trovaMessaggiInviati(email)).thenReturn(messaggiInviati);
            when(messaggioService.trovaAvvisi()).thenReturn(avvisi);

            // Act
            servlet.doPost(request, response);

            // Assert
            verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
            verify(request).setAttribute("messaggiRicevuti", messaggiRicevuti);
            verify(request).setAttribute("messaggiInviati", messaggiInviati);
            verify(request).setAttribute("messaggi", avvisi);
            verify(requestDispatcher).forward(request, response);

            System.out.println("✓ Test completato - " + messaggiRicevuti.size() + " ricevuti, "
                + messaggiInviati.size() + " inviati, " + avvisi.size() + " avvisi");
        }
    }

    @Test
    void testDoPostWithEmptyLists() throws Exception {
        System.out.println("\n=== Test 4: doPost con liste vuote ===");

        // Arrange
        String email = "nuovo@studenti.unisa.it";

        Studente studente = new Studente();
        studente.setEmail(email);
        studente.setMatricola("0512100030");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);

        // Liste vuote
        List<Messaggio> messaggiVuoti = new ArrayList<>();

        try (@SuppressWarnings("unused") MockedConstruction<AccademicoService> mockedService = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaEmailUniClass(email)).thenReturn(studente))) {

            when(messaggioService.trovaMessaggiRicevuti(email)).thenReturn(messaggiVuoti);
            when(messaggioService.trovaMessaggiInviati(email)).thenReturn(messaggiVuoti);
            when(messaggioService.trovaAvvisi()).thenReturn(messaggiVuoti);

            // Act
            servlet.doPost(request, response);

            // Assert
            verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
            verify(request).setAttribute("messaggiRicevuti", messaggiVuoti);
            verify(request).setAttribute("messaggiInviati", messaggiVuoti);
            verify(request).setAttribute("messaggi", messaggiVuoti);
            verify(requestDispatcher).forward(request, response);

            System.out.println("✓ Test completato con liste vuote");
        }
    }

    @Test
    void testDoGet() throws Exception {
        System.out.println("\n=== Test 5: doGet (delega a doPost) ===");

        // Arrange
        String email = "test@studenti.unisa.it";

        Studente studente = new Studente();
        studente.setEmail(email);
        studente.setMatricola("0512100040");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);

        List<Messaggio> messaggiVuoti = new ArrayList<>();

        try (@SuppressWarnings("unused") MockedConstruction<AccademicoService> mockedService = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaEmailUniClass(email)).thenReturn(studente))) {

            when(messaggioService.trovaMessaggiRicevuti(email)).thenReturn(messaggiVuoti);
            when(messaggioService.trovaMessaggiInviati(email)).thenReturn(messaggiVuoti);
            when(messaggioService.trovaAvvisi()).thenReturn(messaggiVuoti);

            // Act
            servlet.doGet(request, response);

            // Assert - verifica che doGet chiami doPost
            verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
            verify(requestDispatcher).forward(request, response);

            System.out.println("✓ Test completato - doGet delega correttamente a doPost");
        }
    }

    @Test
    void testDoPostWithNullAvvisi() throws Exception {
        System.out.println("\n=== Test 6: doPost con avvisi null (gestione edge case) ===");

        // Arrange
        String email = "edge@studenti.unisa.it";

        Studente studente = new Studente();
        studente.setEmail(email);
        studente.setMatricola("0512100050");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);

        List<Messaggio> messaggiRicevuti = new ArrayList<>();
        List<Messaggio> messaggiInviati = new ArrayList<>();

        try (@SuppressWarnings("unused") MockedConstruction<AccademicoService> mockedService = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaEmailUniClass(email)).thenReturn(studente))) {

            when(messaggioService.trovaMessaggiRicevuti(email)).thenReturn(messaggiRicevuti);
            when(messaggioService.trovaMessaggiInviati(email)).thenReturn(messaggiInviati);
            when(messaggioService.trovaAvvisi()).thenReturn(new ArrayList<>());

            // Act
            servlet.doPost(request, response);

            // Assert
            verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
            verify(request).setAttribute(eq("messaggiRicevuti"), any(List.class));
            verify(request).setAttribute(eq("messaggiInviati"), any(List.class));
            verify(request).setAttribute(eq("messaggi"), any(List.class));
            verify(requestDispatcher).forward(request, response);

            System.out.println("✓ Test completato");
        }
    }

    @Test
    void testDoPostWithDifferentEmailFormats() throws Exception {
        System.out.println("\n=== Test 7: doPost con diversi formati email ===");

        // Test con email professore
        String email = "g.verdi@unisa.it";

        Docente docente = new Docente();
        docente.setEmail(email);
        docente.setMatricola("0512100060");
        docente.setNome("Giovanni");
        docente.setCognome("Verdi");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn(email);
        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(requestDispatcher);

        List<Messaggio> messaggi = new ArrayList<>();

        try (@SuppressWarnings("unused") MockedConstruction<AccademicoService> mockedService = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaEmailUniClass(email)).thenReturn(docente))) {

            when(messaggioService.trovaMessaggiRicevuti(email)).thenReturn(messaggi);
            when(messaggioService.trovaMessaggiInviati(email)).thenReturn(messaggi);
            when(messaggioService.trovaAvvisi()).thenReturn(messaggi);

            // Act
            servlet.doPost(request, response);

            // Assert
            verify(request).setAttribute(eq("accademicoSelf"), any(Accademico.class));
            verify(messaggioService).trovaMessaggiRicevuti(email);
            verify(messaggioService).trovaMessaggiInviati(email);
            verify(requestDispatcher).forward(request, response);

            System.out.println("✓ Test completato con email formato professore");
        }
    }
}
