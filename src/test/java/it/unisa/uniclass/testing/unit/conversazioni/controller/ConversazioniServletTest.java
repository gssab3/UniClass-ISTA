package it.unisa.uniclass.testing.unit.conversazioni.controller;

import it.unisa.uniclass.conversazioni.controller.ConversazioniServlet;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class ConversazioniServletTest {

    private ConversazioniServlet servlet;

    @Mock private HttpServletRequest request;
    @Mock private HttpServletResponse response;
    @Mock private HttpSession session;
    @Mock private ServletContext servletContext;
    @Mock private RequestDispatcher dispatcher;

    // Servizi da iniettare
    @Mock private MessaggioService messaggioService;
    @Mock private UserDirectory userDirectory;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new ConversazioniServlet();

        // Inject MessaggioService
        Field msgField = ConversazioniServlet.class.getDeclaredField("messaggioService");
        msgField.setAccessible(true);
        msgField.set(servlet, messaggioService);

        // Inject UserDirectory
        Field userField = ConversazioniServlet.class.getDeclaredField("userDirectory");
        userField.setAccessible(true);
        userField.set(servlet, userDirectory);

        // Mock base
        lenient().when(request.getSession()).thenReturn(session);
        lenient().when(request.getServletContext()).thenReturn(servletContext);
    }

    @Test
    @DisplayName("DoPost: Redirect a Login se sessione scaduta o email null")
    void testDoPost_NoSession() throws IOException {
        when(session.getAttribute("utenteEmail")).thenReturn(null);

        servlet.doPost(request, response);

        verify(response).sendRedirect("Login.jsp");
        verify(userDirectory, never()).getAccademico(anyString());
    }

    @Test
    @DisplayName("DoPost: Errore 403 se utente non è Accademico (getAccademico ritorna null)")
    void testDoPost_NotAccademico() throws IOException {
        when(session.getAttribute("utenteEmail")).thenReturn("user@unisa.it");
        when(userDirectory.getAccademico("user@unisa.it")).thenReturn(null);

        servlet.doPost(request, response);

        verify(response).sendError(HttpServletResponse.SC_FORBIDDEN, "Accesso consentito solo agli accademici.");
    }

    @Test
    @DisplayName("DoPost: Successo - Caricamento messaggi e Lazy Load Fix")
    void testDoPost_Success() throws Exception {
        // Arrange User
        String email = "prof@unisa.it";
        String matricola = "0001";
        when(session.getAttribute("utenteEmail")).thenReturn(email);

        Accademico self = mock(Accademico.class);
        when(self.getMatricola()).thenReturn(matricola);
        when(userDirectory.getAccademico(email)).thenReturn(self);

        // Arrange Messages & Lazy Loading
        List<Messaggio> inviati = new ArrayList<>();
        Messaggio m1 = new Messaggio();
        m1.setAutore(self); // autore non null
        m1.setDestinatario(new Accademico()); // dest non null
        m1.setTopic(new Topic()); // topic non null
        inviati.add(m1);

        List<Messaggio> ricevuti = new ArrayList<>();
        Messaggio m2 = new Messaggio(); // Campi null per testare i check if
        ricevuti.add(m2);

        when(messaggioService.trovaMessaggiInviati(matricola)).thenReturn(inviati);
        when(messaggioService.trovaMessaggiRicevuti(matricola)).thenReturn(ricevuti);
        when(messaggioService.trovaAvvisi()).thenReturn(new ArrayList<>());

        when(request.getRequestDispatcher("Conversazioni.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doPost(request, response);

        // Assert
        // Verifica fix lazy load su m1
        verify(self, atLeastOnce()).getNome();

        // Verifica attributi settati
        verify(request).setAttribute("accademicoSelf", self);
        verify(request).setAttribute("messaggiInviati", inviati);
        verify(request).setAttribute("messaggiRicevuti", ricevuti);

        // Verifica forward
        verify(dispatcher).forward(request, response);
    }

    @Test
    @DisplayName("DoGet: Delega a DoPost")
    void testDoGet() {
        // Setup minimo per far passare DoPost senza errori fino al redirect
        when(session.getAttribute("utenteEmail")).thenReturn(null);

        servlet.doGet(request, response);

        try {
            verify(response).sendRedirect(anyString());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Test
    @DisplayName("Gestione Eccezioni Generiche")
    void testException() throws IOException {
        when(request.getSession()).thenThrow(new RuntimeException("Crash"));

        servlet.doPost(request, response);

        verify(servletContext).log(eq("Error processing conversazioni request"), any(RuntimeException.class));
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
    }
}