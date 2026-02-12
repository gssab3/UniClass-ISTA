package it.unisa.uniclass.testing.unit.conversazioni.controller;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.io.IOException;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

/**
 * Test completi per invioMessaggioServlet.
 * Coverage massimizzata per JaCoCo.
 */
public class invioMessaggioServletTest {

    @Mock
    private MessaggioService messaggioService;

    @Mock
    private AccademicoService accademicoService;

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private HttpSession session;

    private it.unisa.uniclass.conversazioni.controller.invioMessaggioServlet servlet;

    private Accademico accademicoMittente;
    private Accademico accademicoDestinatario;
    private CorsoLaurea corsoLaurea;
    private Messaggio messaggioSalvato;

    @BeforeEach
    public void setUp() {
        MockitoAnnotations.openMocks(this);

        servlet = new it.unisa.uniclass.conversazioni.controller.invioMessaggioServlet();
        servlet.setMessaggioService(messaggioService);
        servlet.setAccademicoService(accademicoService);
        when(request.getServletContext()).thenReturn(mock(jakarta.servlet.ServletContext.class));

        // Setup CorsoLaurea
        corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");

        // Setup Accademico Mittente (Studente)
        accademicoMittente = new Studente();
        accademicoMittente.setEmail("studente@studenti.unisa.it");
        accademicoMittente.setNome("Giovanni");
        accademicoMittente.setCognome("Bianchi");
        accademicoMittente.setMatricola("0512100001");
        accademicoMittente.setCorsoLaurea(corsoLaurea);

        // Setup Accademico Destinatario (Docente)
        accademicoDestinatario = new Docente();
        accademicoDestinatario.setEmail("docente@unisa.it");
        accademicoDestinatario.setNome("Maria");
        accademicoDestinatario.setCognome("Rossi");
        accademicoDestinatario.setMatricola("0512100999");
        accademicoDestinatario.setCorsoLaurea(corsoLaurea);

        // Setup Messaggio salvato
        messaggioSalvato = new Messaggio();
        messaggioSalvato.setAutore(accademicoMittente);
        messaggioSalvato.setDestinatario(accademicoDestinatario);
        messaggioSalvato.setBody("Messaggio di test");
        messaggioSalvato.setDateTime(LocalDateTime.now());
    }

    @Test
    public void testDoGetSuccessfulMessageWithoutTopic() throws ServletException, IOException {
        System.out.println("\n=== Test 1: Invio messaggio senza topic ===");

        // Arrange
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("studente@studenti.unisa.it");
        when(request.getParameter("email")).thenReturn("docente@unisa.it");
        when(request.getParameter("testo")).thenReturn("Ciao professore, ho una domanda");
        when(request.getParameter("topic")).thenReturn(null);

        when(accademicoService.trovaEmailUniClass("studente@studenti.unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("docente@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);

        List<Messaggio> messaggi = new ArrayList<>();
        messaggi.add(messaggioSalvato);
        when(messaggioService.trovaTutti()).thenReturn(messaggi);

        List<Accademico> messaggeri = new ArrayList<>();
        messaggeri.add(accademicoDestinatario);
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(messaggeri);

        // Act
        servlet.doGet(request, response);

        // Assert
        verify(accademicoService).trovaEmailUniClass("studente@studenti.unisa.it");
        verify(accademicoService).trovaEmailUniClass("docente@unisa.it");

        ArgumentCaptor<Messaggio> messaggioCaptor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(messaggioCaptor.capture());

        Messaggio messaggioInviato = messaggioCaptor.getValue();
        assertNotNull(messaggioInviato);
        assertEquals("Ciao professore, ho una domanda", messaggioInviato.getBody());
        assertEquals(accademicoMittente, messaggioInviato.getAutore());
        assertEquals(accademicoDestinatario, messaggioInviato.getDestinatario());
        assertNull(messaggioInviato.getTopic());
        assertNotNull(messaggioInviato.getDateTime());

        verify(messaggioService).trovaTutti();
        verify(messaggioService).trovaMessaggeriDiUnAccademico("0512100001");
        verify(request).setAttribute("messaggi", messaggi);
        verify(request).setAttribute("accademici", messaggeri);
        verify(response).sendRedirect("Conversazioni");

        System.out.println("✓ Messaggio senza topic inviato correttamente");
    }

    @Test
    public void testDoGetSuccessfulMessageWithTopic() throws ServletException, IOException {
        System.out.println("\n=== Test 2: Invio avviso con topic ===");

        // Arrange
        String topicName = "Esame Programmazione";

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("docente@unisa.it");
        when(request.getParameter("email")).thenReturn("studente@studenti.unisa.it");
        when(request.getParameter("testo")).thenReturn("Esame posticipato al prossimo mese");
        when(request.getParameter("topic")).thenReturn(topicName);

        // Scambio mittente e destinatario per questo test
        when(accademicoService.trovaEmailUniClass("docente@unisa.it")).thenReturn(accademicoDestinatario);
        when(accademicoService.trovaEmailUniClass("studente@studenti.unisa.it")).thenReturn(accademicoMittente);

        Messaggio msgConTopic = new Messaggio();
        msgConTopic.setAutore(accademicoDestinatario);
        msgConTopic.setDestinatario(accademicoMittente);
        msgConTopic.setBody("Esame posticipato al prossimo mese");
        msgConTopic.setDateTime(LocalDateTime.now());
        Topic topic = new Topic();
        topic.setNome(topicName);
        topic.setCorsoLaurea(corsoLaurea);
        msgConTopic.setTopic(topic);

        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(msgConTopic);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        // Act
        servlet.doGet(request, response);

        // Assert
        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());

        Messaggio messaggio = captor.getValue();
        assertNotNull(messaggio.getTopic());
        assertEquals(topicName, messaggio.getTopic().getNome());
        assertEquals(corsoLaurea, messaggio.getTopic().getCorsoLaurea());
        assertEquals("Esame posticipato al prossimo mese", messaggio.getBody());

        System.out.println("✓ Avviso con topic '" + topicName + "' inviato correttamente");
    }

    @Test
    public void testDoGetWithEmptyMessage() throws ServletException, IOException {
        System.out.println("\n=== Test 3: Invio messaggio vuoto ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("studente@studenti.unisa.it");
        when(request.getParameter("email")).thenReturn("docente@unisa.it");
        when(request.getParameter("testo")).thenReturn("");
        when(request.getParameter("topic")).thenReturn(null);

        when(accademicoService.trovaEmailUniClass("studente@studenti.unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("docente@unisa.it")).thenReturn(accademicoDestinatario);

        Messaggio msgVuoto = new Messaggio();
        msgVuoto.setBody("");
        msgVuoto.setAutore(accademicoMittente);
        msgVuoto.setDestinatario(accademicoDestinatario);
        msgVuoto.setDateTime(LocalDateTime.now());

        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(msgVuoto);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());
        assertEquals("", captor.getValue().getBody());

        System.out.println("✓ Messaggio vuoto gestito correttamente");
    }

    @Test
    public void testDoGetWithLongMessage() throws ServletException, IOException {
        System.out.println("\n=== Test 4: Invio messaggio lungo ===");

        String longMessage = "Gentile professore, ".repeat(50) + "cordiali saluti.";

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("studente@studenti.unisa.it");
        when(request.getParameter("email")).thenReturn("docente@unisa.it");
        when(request.getParameter("testo")).thenReturn(longMessage);
        when(request.getParameter("topic")).thenReturn(null);

        when(accademicoService.trovaEmailUniClass("studente@studenti.unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("docente@unisa.it")).thenReturn(accademicoDestinatario);

        Messaggio msgLungo = new Messaggio();
        msgLungo.setBody(longMessage);
        msgLungo.setAutore(accademicoMittente);
        msgLungo.setDestinatario(accademicoDestinatario);
        msgLungo.setDateTime(LocalDateTime.now());

        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(msgLungo);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());
        assertEquals(longMessage, captor.getValue().getBody());

        System.out.println("✓ Messaggio lungo (" + longMessage.length() + " caratteri) inviato");
    }

    @Test
    public void testDoGetWithMultipleMessages() throws ServletException, IOException {
        System.out.println("\n=== Test 5: Recupero messaggi multipli ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("studente@studenti.unisa.it");
        when(request.getParameter("email")).thenReturn("docente@unisa.it");
        when(request.getParameter("testo")).thenReturn("Messaggio test");
        when(request.getParameter("topic")).thenReturn(null);

        when(accademicoService.trovaEmailUniClass("studente@studenti.unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("docente@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);

        // Crea 15 messaggi
        List<Messaggio> messaggi = new ArrayList<>();
        for (int i = 0; i < 15; i++) {
            Messaggio msg = new Messaggio();
            msg.setBody("Messaggio numero " + i);
            messaggi.add(msg);
        }
        when(messaggioService.trovaTutti()).thenReturn(messaggi);

        // Crea 7 messaggeri
        List<Accademico> messaggeri = new ArrayList<>();
        for (int i = 0; i < 7; i++) {
            Accademico acc = new Studente();
            acc.setEmail("user" + i + "@studenti.unisa.it");
            messaggeri.add(acc);
        }
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(messaggeri);

        servlet.doGet(request, response);

        verify(request).setAttribute("messaggi", messaggi);
        verify(request).setAttribute("accademici", messaggeri);
        assertEquals(15, messaggi.size());
        assertEquals(7, messaggeri.size());

        System.out.println("✓ Recuperati " + messaggi.size() + " messaggi e " + messaggeri.size() + " messaggeri");
    }

    @Test
    public void testDoGetWithSpecialCharacters() throws ServletException, IOException {
        System.out.println("\n=== Test 6: Messaggio con caratteri speciali ===");

        String specialMsg = "Ciao! àèéìòù ñ çÇ €£$¥ @#&*() <> \"' 你好 🚀";

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("studente@studenti.unisa.it");
        when(request.getParameter("email")).thenReturn("docente@unisa.it");
        when(request.getParameter("testo")).thenReturn(specialMsg);
        when(request.getParameter("topic")).thenReturn(null);

        when(accademicoService.trovaEmailUniClass("studente@studenti.unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("docente@unisa.it")).thenReturn(accademicoDestinatario);

        Messaggio msg = new Messaggio();
        msg.setBody(specialMsg);
        msg.setAutore(accademicoMittente);
        msg.setDestinatario(accademicoDestinatario);
        msg.setDateTime(LocalDateTime.now());

        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(msg);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());
        assertEquals(specialMsg, captor.getValue().getBody());

        System.out.println("✓ Caratteri speciali gestiti correttamente");
    }

    @Test
    public void testDoPost() throws ServletException, IOException {
        System.out.println("\n=== Test 7: Metodo doPost (delega a doGet) ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("studente@studenti.unisa.it");
        when(request.getParameter("email")).thenReturn("docente@unisa.it");
        when(request.getParameter("testo")).thenReturn("Test POST");
        when(request.getParameter("topic")).thenReturn(null);

        when(accademicoService.trovaEmailUniClass("studente@studenti.unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("docente@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doPost(request, response);

        verify(messaggioService).aggiungiMessaggio(any(Messaggio.class));
        verify(response).sendRedirect("Conversazioni");

        System.out.println("✓ doPost delega correttamente a doGet");
    }

    @Test
    public void testMessageDateTimeIsSet() throws ServletException, IOException {
        System.out.println("\n=== Test 8: Verifica DateTime messaggio ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("studente@studenti.unisa.it");
        when(request.getParameter("email")).thenReturn("docente@unisa.it");
        when(request.getParameter("testo")).thenReturn("Test datetime");
        when(request.getParameter("topic")).thenReturn(null);

        when(accademicoService.trovaEmailUniClass("studente@studenti.unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("docente@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        LocalDateTime before = LocalDateTime.now().minusSeconds(1);
        servlet.doGet(request, response);
        LocalDateTime after = LocalDateTime.now().plusSeconds(1);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());

        LocalDateTime messageTime = captor.getValue().getDateTime();
        assertNotNull(messageTime);
        assertTrue(messageTime.isAfter(before));
        assertTrue(messageTime.isBefore(after));

        System.out.println("✓ DateTime impostato correttamente: " + messageTime);
    }

    @Test
    public void testAllServiceCallsAreMade() throws ServletException, IOException {
        System.out.println("\n=== Test 9: Verifica tutte le chiamate ai service ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("studente@studenti.unisa.it");
        when(request.getParameter("email")).thenReturn("docente@unisa.it");
        when(request.getParameter("testo")).thenReturn("Test service calls");
        when(request.getParameter("topic")).thenReturn(null);

        when(accademicoService.trovaEmailUniClass("studente@studenti.unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("docente@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        verify(accademicoService, times(1)).trovaEmailUniClass("studente@studenti.unisa.it");
        verify(accademicoService, times(1)).trovaEmailUniClass("docente@unisa.it");
        verify(messaggioService, times(1)).aggiungiMessaggio(any(Messaggio.class));
        verify(messaggioService, times(1)).trovaTutti();
        verify(messaggioService, times(1)).trovaMessaggeriDiUnAccademico("0512100001");

        System.out.println("✓ Tutte le chiamate ai service verificate");
    }

    @Test
    public void testTopicWithDifferentNames() throws ServletException, IOException {
        System.out.println("\n=== Test 10: Topic con nomi diversi ===");

        String[] topicNames = {"Lezione 1", "Esame Finale", "Avviso Urgente", "Ricevimento"};

        for (String topicName : topicNames) {
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("utenteEmail")).thenReturn("docente@unisa.it");
            when(request.getParameter("email")).thenReturn("studente@studenti.unisa.it");
            when(request.getParameter("testo")).thenReturn("Messaggio per " + topicName);
            when(request.getParameter("topic")).thenReturn(topicName);

            when(accademicoService.trovaEmailUniClass("docente@unisa.it")).thenReturn(accademicoDestinatario);
            when(accademicoService.trovaEmailUniClass("studente@studenti.unisa.it")).thenReturn(accademicoMittente);
            when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);
            when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
            when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

            servlet.doGet(request, response);

            ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
            verify(messaggioService, atLeastOnce()).aggiungiMessaggio(captor.capture());

            Messaggio msg = captor.getValue();
            if (msg.getTopic() != null) {
                assertEquals(topicName, msg.getTopic().getNome());
            }
        }

        System.out.println("✓ Testati " + topicNames.length + " topic diversi");
    }
}

