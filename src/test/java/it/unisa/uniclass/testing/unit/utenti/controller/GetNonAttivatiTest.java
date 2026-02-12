package it.unisa.uniclass.testing.unit.utenti.controller;

import it.unisa.uniclass.utenti.controller.GetNonAttivati;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.servlet.ServletContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class GetNonAttivatiTest {

    // Wrapper per esporre i metodi protected
    static class TestableGetNonAttivati extends GetNonAttivati {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) {
            super.doGet(req, resp);
        }

        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp) {
            super.doPost(req, resp);
        }
    }

    private TestableGetNonAttivati servlet;

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private UserDirectory userDirectory;

    @Mock
    private ServletContext servletContext;

    private StringWriter stringWriter;
    private PrintWriter printWriter;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new TestableGetNonAttivati();

        // Iniezione manuale del Mock via Reflection
        Field field = GetNonAttivati.class.getDeclaredField("userDirectory");
        field.setAccessible(true);
        field.set(servlet, userDirectory);

        // Setup Response Writer per catturare il JSON
        stringWriter = new StringWriter();
        printWriter = new PrintWriter(stringWriter);
        lenient().when(response.getWriter()).thenReturn(printWriter);

        // Setup Context per i log
        lenient().when(request.getServletContext()).thenReturn(servletContext);
    }

    @Test
    @DisplayName("DoGet: Filtra correttamente e gestisce il ternario sul Ruolo")
    void testDoGet_Logic() {
        // Arrange - Creiamo casi per coprire tutti i rami (Branch Coverage)

        // Caso 1: Accademico NON attivato (Target del filtro) - Ruolo Presente
        Accademico target1 = new Accademico();
        target1.setEmail("target@unisa.it");
        target1.setMatricola("0512101");
        target1.setAttivato(false);
        target1.setRuolo(Ruolo.STUDENTE);

        // Caso 2: Accademico NON attivato - Ruolo NULL (Branch coverage ternario)
        Accademico target2 = new Accademico();
        target2.setEmail("norole@unisa.it");
        target2.setMatricola("0512102");
        target2.setAttivato(false);
        target2.setRuolo(null); // Forza ramo 'else' del ternario

        // Caso 3: Accademico GIA' attivato (Deve essere escluso)
        Accademico activeAcc = new Accademico();
        activeAcc.setEmail("active@unisa.it");
        activeAcc.setAttivato(true);

        // Caso 4: Utente generico (Deve essere escluso - instanceOf false)
        Utente simpleUser = new Utente();
        simpleUser.setEmail("simple@unisa.it");

        List<Utente> list = Arrays.asList(target1, target2, activeAcc, simpleUser);
        when(userDirectory.getTuttiGliUtenti()).thenReturn(list);

        // Act
        servlet.doGet(request, response);

        // Assert
        String jsonOutput = stringWriter.toString();

        // Verifica Presenza Target 1
        assertTrue(jsonOutput.contains("target@unisa.it"));
        assertTrue(jsonOutput.contains("0512101"));
        assertTrue(jsonOutput.contains("STUDENTE"));

        // Verifica Presenza Target 2 (Ruolo null -> stringa vuota o null nel json)
        assertTrue(jsonOutput.contains("norole@unisa.it"));
        // Se il ruolo è null, il codice mette "" -> verifichiamo che non esploda e sia presente

        // Verifica Assenza Esclusi
        assertFalse(jsonOutput.contains("active@unisa.it"), "Utenti attivi non dovrebbero esserci");
        assertFalse(jsonOutput.contains("simple@unisa.it"), "Utenti non accademici non dovrebbero esserci");

        verify(response).setContentType("application/json");
        verify(response).setCharacterEncoding("UTF-8");
    }

    @Test
    @DisplayName("DoGet: Lista vuota restituisce JSON array vuoto")
    void testDoGet_Empty() {
        when(userDirectory.getTuttiGliUtenti()).thenReturn(Collections.emptyList());

        servlet.doGet(request, response);

        String jsonOutput = stringWriter.toString();
        assertEquals("[]", jsonOutput);
    }

    @Test
    @DisplayName("DoGet: Gestione Eccezione (Log e 500)")
    void testDoGet_Exception() throws IOException {
        when(userDirectory.getTuttiGliUtenti()).thenThrow(new RuntimeException("DB Crash"));

        servlet.doGet(request, response);

        verify(servletContext).log(eq("Error processing GetNonAttivati"), any(RuntimeException.class));
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
    }

    @Test
    @DisplayName("DoPost: Delega a DoGet")
    void testDoPost_Delegates() {
        when(userDirectory.getTuttiGliUtenti()).thenReturn(Collections.emptyList());

        servlet.doPost(request, response);

        verify(userDirectory).getTuttiGliUtenti(); // Conferma esecuzione logica
    }
}